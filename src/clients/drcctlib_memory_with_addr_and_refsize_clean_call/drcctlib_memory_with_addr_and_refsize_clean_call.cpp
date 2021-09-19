/* 
 *  Copyright (c) 2020-2021 Xuhpclab. All rights reserved.
 *  Licensed under the MIT License.
 *  See LICENSE file for more information.
 */

#include <cstddef>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <iostream>
#include <unistd.h>
#include <unordered_map>
#include <sys/mman.h>
#include <functional>
#include <vector>

#include "dr_api.h"
#include "drmgr.h"
#include "drreg.h"
#include "drutil.h"
#include "drcctlib.h"

using namespace std;

#define DRCCTLIB_PRINTF(_FORMAT, _ARGS...) \
    DRCCTLIB_PRINTF_TEMPLATE("memory_with_addr_and_refsize_clean_call", _FORMAT, ##_ARGS)
#define DRCCTLIB_EXIT_PROCESS(_FORMAT, _ARGS...)                                           \
    DRCCTLIB_CLIENT_EXIT_PROCESS_TEMPLATE("memory_with_addr_and_refsize_clean_call", _FORMAT, \
                                          ##_ARGS)

static int tls_idx;
static int memOp_num; 
static int zero = 0;

// __thread bool Sample_flag = true;
// __thread long long NUM_INS = 0;
thread_local bool Sample_flag = true;
thread_local long long NUM_INS = 0;

#define TLS_MEM_REF_BUFF_SIZE 100
#define WINDOW_ENABLE 1000000
#define WINDOW_DISABLE 1000000000
#define MAX_WRITE_OP_LENGTH (512)
#define MAX_WRITE_OPS_IN_INS (8)
#define THREAD_MAX (1024)

/* infrastructure for shadow memory */
/* MACROs */
// 64KB shadow pages
#define PAGE_OFFSET_BITS (16LL)
#define PAGE_OFFSET(addr) ( addr & 0xFFFF)
#define PAGE_OFFSET_MASK ( 0xFFFF)

#define PAGE_SIZE (1 << PAGE_OFFSET_BITS)

// 2 level page table
#define PTR_SIZE (sizeof(struct Status *))
#define LEVEL_1_PAGE_TABLE_BITS  (20)
#define LEVEL_1_PAGE_TABLE_ENTRIES  (1 << LEVEL_1_PAGE_TABLE_BITS )
#define LEVEL_1_PAGE_TABLE_SIZE  (LEVEL_1_PAGE_TABLE_ENTRIES * PTR_SIZE )

#define LEVEL_2_PAGE_TABLE_BITS  (12)
#define LEVEL_2_PAGE_TABLE_ENTRIES  (1 << LEVEL_2_PAGE_TABLE_BITS )
#define LEVEL_2_PAGE_TABLE_SIZE  (LEVEL_2_PAGE_TABLE_ENTRIES * PTR_SIZE )

#define LEVEL_1_PAGE_TABLE_SLOT(addr) (((addr) >> (LEVEL_2_PAGE_TABLE_BITS + PAGE_OFFSET_BITS)) & 0xfffff)
#define LEVEL_2_PAGE_TABLE_SLOT(addr) (((addr) >> (PAGE_OFFSET_BITS)) & 0xFFF)

#define IS_ACCESS_WITHIN_PAGE_BOUNDARY(accessAddr, accessLen) (PAGE_OFFSET((accessAddr)) <= (PAGE_OFFSET_MASK - (accessLen)))

#define MAKE_CONTEXT_PAIR(a, b) (((uint64_t)(a) << 32) | ((uint64_t)(b)))

static file_t gTraceFile;
static uint8_t** gL1PageTable[LEVEL_1_PAGE_TABLE_SIZE];


enum {
    INSTRACE_TLS_OFFS_BUF_PTR,
    INSTRACE_TLS_COUNT, /* total number of TLS slots allocated */
};
static reg_id_t tls_seg;
static uint tls_offs;
#define TLS_SLOT(tls_base, enum_val) (void **)((byte *)(tls_base) + tls_offs + (enum_val))
#define BUF_PTR(tls_base, type, offs) *(type **)TLS_SLOT(tls_base, offs)
#define MINSERT instrlist_meta_preinsert
#ifdef ARM_CCTLIB
#    define OPND_CREATE_CCT_INT OPND_CREATE_INT
#else
#    define OPND_CREATE_CCT_INT OPND_CREATE_INT32
#endif

typedef struct _mem_ref_t {
    app_pc addr;
    size_t size;
} mem_ref_t;

typedef struct op_ref{
    uint64_t *opAddr;
    uint32_t opSize;
}op_ref;

typedef struct _per_thread_t {
    mem_ref_t *cur_buf_list;
    void *cur_buf;
    op_ref opList[MAX_WRITE_OPS_IN_INS];
    //uint64_t opList[MAX_WRITE_OPS_IN_INS];
    uint64_t value[MAX_WRITE_OPS_IN_INS];
    uint64_t bytesWritten;
} per_thread_t;

typedef struct AddrValPair {
    void *address;
    uint8_t value[MAX_WRITE_OP_LENGTH];
} AddrValPair;

typedef struct RedSpyThreadData {
    AddrValPair buffer[MAX_WRITE_OPS_IN_INS];
    uint64_t bytesWritten;
} RedSpyThreadData;

static unordered_map<uint64_t, uint64_t> RedMap[THREAD_MAX];
static void AddToRedTable(uint64_t key, uint16_t value, int threadID){
#ifdef MULTI_THREADED
    //LOCK_RED_MAP();
#endif
    unordered_map<uint64_t, uint64_t>::iterator it = RedMap[threadID].find(key);
    if (it == RedMap[threadID].end()) {
        RedMap[threadID][key] = value;
    } else {
        it->second += value;
    }
#ifdef MULTI_THREADED
    //UNLOCK_RED_MAP();
#endif
}


// to access thread-specific data
inline RedSpyThreadData* ClientGetTLS(void *drcontext){
    RedSpyThreadData *tdata = static_cast<RedSpyThreadData*>(drmgr_get_tls_field(drcontext, tls_idx));
    return tdata;
}

template<int start, int end, int incr>
struct UnrolledConjunction{
    static bool Body(function<bool (const int)> func){
        return func(start) && UnrolledConjunction<start+incr, end, incr>::Body(func); // unroll next iteration
    }
};

template<int end, int incr>
struct UnrolledConjunction<end, end, incr>{
    static bool Body(function<void (const int)> func){
        return true;
    }
};

// helper functions for shadow memory
static uint8_t* GetOrCreateShadowBaseAddress(uint64_t addr){
    uint8_t *shadowPage;
    uint8_t** *l1Ptr = &gL1PageTable[LEVEL_1_PAGE_TABLE_SLOT(addr)];

    if(*l1Ptr == 0){
        *l1Ptr = (uint8_t**)mmap(0, LEVEL_2_PAGE_TABLE_SIZE, PROT_WRITE | PROT_READ, MAP_NORESERVE | MAP_PRIVATE | MAP_ANONYMOUS, 0, 0);
        shadowPage = (*l1Ptr)[LEVEL_2_PAGE_TABLE_SLOT(addr)] = (uint8_t*) mmap(0, PAGE_SIZE * (sizeof(uint64_t)), PROT_WRITE | PROT_READ, MAP_NORESERVE | MAP_PRIVATE | MAP_ANONYMOUS, 0, 0);
    }else if((shadowPage = (*l1Ptr)[LEVEL_2_PAGE_TABLE_SLOT(addr)]) == 0 ){
        shadowPage = (*l1Ptr)[LEVEL_2_PAGE_TABLE_SLOT(addr)] = (uint8_t*) mmap(0, PAGE_SIZE * (sizeof(uint64_t)), PROT_WRITE | PROT_READ, MAP_NORESERVE | MAP_PRIVATE | MAP_ANONYMOUS, 0, 0);
    }
    return shadowPage;
}


template<uint16_t AccessLen, uint32_t bufferOffset>
struct RedSpyAnalysis{
    static void RecordNByteValueBeforeWrite(void *addr, void* drcontext, uint32_t memOp){
        if(Sample_flag){
            NUM_INS++;
            if(NUM_INS > WINDOW_ENABLE){
                Sample_flag = false;
                NUM_INS = 0;
                return;
            }
        }else{
            NUM_INS++;
            if(NUM_INS > WINDOW_DISABLE){
                Sample_flag = true;
                NUM_INS = 0;
            }else{
                return;
            }
        }
        //dr_fprintf(gTraceFile, "AccessLen = %d\n", AccessLen);
        per_thread_t *pt = (per_thread_t *)drmgr_get_tls_field(drcontext, tls_idx);
        pt->bytesWritten += AccessLen;
        
        //dr_fprintf(gTraceFile, "bytewritten = %llu\n", pt->bytesWritten);
        //dr_fprintf(gTraceFile, "addr = %p\n", addr);
        //*((uint64_t *)(&(pt->value[memOp]))) = *(static_cast<uint64_t*>(addr));
        
        switch(AccessLen) {
            case 1: 
                uint8_t temp1;
                if (!dr_safe_read(addr, 1, &temp1, NULL))
                    return;
                //dr_fprintf(gTraceFile, "before value = %" PRIu8 "\n", *((uint8_t *)(&(pt->value[memOp]))));
                *((uint8_t *)(&(pt->value[memOp]))) = temp1;
                //dr_fprintf(gTraceFile, "after value = %" PRIu8 "\n", *((uint8_t *)(&(pt->value[memOp]))));
                break;
            case 2:
                //*((uint16_t*)(pt->value[memOp])) = *(static_cast<uint16_t*>(addr));
                uint16_t temp2;
                if (!dr_safe_read(addr, 2, &temp2, NULL))
                    return;
                //dr_fprintf(gTraceFile, "before value = %u\n", *((uint16_t *)(&(pt->value[memOp]))));
                *((uint16_t *)(&(pt->value[memOp]))) = temp2;
                //dr_fprintf(gTraceFile, "after value = %u\n", *((uint16_t *)(&(pt->value[memOp]))));
                break;
            case 4:
                uint32_t temp4;
                if (!dr_safe_read(addr, 4, &temp4, NULL))
                    return;
                //dr_fprintf(gTraceFile, "before value = %lu\n", *((uint32_t *)(&(pt->value[memOp]))));
                *((uint32_t *)(&(pt->value[memOp]))) = temp4;
                //dr_fprintf(gTraceFile, "after value = %lu\n", *((uint32_t *)(&(pt->value[memOp]))));
                //*((uint32_t*)(pt->value[memOp])) = *(static_cast<uint32_t*>(addr));
                break;
            case 8: 
                // store the value of addr to temp8
                uint64_t temp8;
                if (!dr_safe_read(addr, 8, &temp8, NULL))
                    return;
                //dr_fprintf(gTraceFile, "!!!!!!!!temp8 is %lu\n", temp8);
                //dr_fprintf(gTraceFile, "1. before value = %llu\n", *((uint64_t *)(&(pt->value[memOp]))));
                *((uint64_t *)(&(pt->value[memOp]))) = temp8;
                //dr_fprintf(gTraceFile, "2. after value = %llu\n", *((uint64_t *)(&(pt->value[memOp]))));
                dr_fprintf(gTraceFile, "(1) addr value = %llu\n", *((uint64_t *)(&(pt->value[memOp]))));
                //*((uint64_t*)(pt->value[memOp])) = *(static_cast<uint64_t*>(addr));
                break;
            //default:
                //TODO 
                //break;
        }
    }

    
    static void CheckNByteValueAfterWrite(void* opAddr, void* drcontext, context_handle_t cur_ctxt_hndl, uint32_t memOp){
        if(!Sample_flag){
            return;
        }
        bool isRedundantWrite = false;
        per_thread_t *pt = (per_thread_t *)drmgr_get_tls_field(drcontext, tls_idx);
        switch(AccessLen) {
            case 1:{
                uint8_t temp1;
                if (!dr_safe_read(opAddr, 1, &temp1, NULL))
                    return;
                //dr_fprintf(gTraceFile, "(2) new temp1 is %" PRIu8 "\n", temp1);
                if (*((uint8_t *)(&(pt->value[memOp]))) == temp1){
                    //dr_fprintf(gTraceFile, "in case 1, equal\n");
                    isRedundantWrite = true;
                    if (temp1 == 0){
                        zero++;
                    }
                }
                break;
            }
            case 2:{
                uint16_t temp2;
                if (!dr_safe_read(opAddr, 2, &temp2, NULL))
                    return;
                if (*((uint16_t *)(&(pt->value[memOp]))) == temp2){
                    //dr_fprintf(gTraceFile, "in case 2, equal\n");
                    isRedundantWrite = true;
                    if (temp2 == 0){
                        zero++;
                    }
                }
                break;
            }
            case 4:{
                uint32_t temp4;
                if (!dr_safe_read(opAddr, 4, &temp4, NULL))
                    return;
                if (*((uint32_t *)(&(pt->value[memOp]))) == temp4){
                    //dr_fprintf(gTraceFile, "in case 4, equal\n");
                    isRedundantWrite = true;
                    if (temp4 == 0){
                        zero++;
                    }
                }
                break;
            }
            case 8:{
                // store the value of opAddr to temp8
                uint64_t temp8;
                if (!dr_safe_read(opAddr, 8, &temp8, NULL))
                    return;
                dr_fprintf(gTraceFile, "(2) new temp8 is %lu\n", temp8);
                // compare the before and after value in opAddr
                if (*((uint64_t *)(&(pt->value[memOp]))) == temp8){
                    //dr_fprintf(gTraceFile, "in case 8, equal\n");
                    isRedundantWrite = true;
                    if (temp8 == 0){
                        zero++;
                    }
                }
                break;
            }
            //default:
                //break;
        }
        //dr_fprintf(gTraceFile, "zero = %d\n", zero);
        dr_fprintf(gTraceFile, "bool = %d\n", isRedundantWrite);

        uint8_t *status = GetOrCreateShadowBaseAddress((uint64_t)opAddr);
        dr_fprintf(gTraceFile, "size of = ")
        bool isAccessWithinPageBoundary = IS_ACCESS_WITHIN_PAGE_BOUNDARY((uint64_t)opAddr, AccessLen);
        // context_handle_t: int32_t

    }
};

template<uint32_t readBufferSlotIndex>
struct RedSpyInstrument{
    static void InstrumentValueBeforeWriting(void *drcontext, context_handle_t cur_ctxt_hndl, mem_ref_t *ref, uint32_t memOp){
        // get address and size of memOp
        void *addr = ref->addr;
        uint32_t refSize = ref->size;
        //dr_fprintf(gTraceFile, "refSize = %d\n", refSize);
        switch(refSize) {
            case 1:
                RedSpyAnalysis<1, readBufferSlotIndex>::RecordNByteValueBeforeWrite(addr, drcontext, memOp);
                break;
            case 2:
                RedSpyAnalysis<2, readBufferSlotIndex>::RecordNByteValueBeforeWrite(addr, drcontext, memOp);
                break;
            case 4:
                RedSpyAnalysis<4, readBufferSlotIndex>::RecordNByteValueBeforeWrite(addr, drcontext, memOp);
                break;
            case 8:
                RedSpyAnalysis<8, readBufferSlotIndex>::RecordNByteValueBeforeWrite(addr, drcontext, memOp);
                break;
            case 10:
                RedSpyAnalysis<10, readBufferSlotIndex>::RecordNByteValueBeforeWrite(addr, drcontext, memOp);
                break;
            case 16:
                RedSpyAnalysis<16, readBufferSlotIndex>::RecordNByteValueBeforeWrite(addr, drcontext, memOp);
                break;
            default:
                // TODO
                // RecordValueBeforeLargeWrite();
                break;
        }

    }
    static void InstrumentValueAfterWriting(void *drcontext, context_handle_t cur_ctxt_hndl, op_ref *opList, uint32_t memOp){
        void *opAddr = opList->opAddr;
        uint32_t opSize = opList->opSize;
        //dr_fprintf(gTraceFile, "opSize = %d\n", opSize);
        switch(opSize) {
            case 1:
                RedSpyAnalysis<1, readBufferSlotIndex>::CheckNByteValueAfterWrite(opAddr, drcontext, cur_ctxt_hndl, memOp);
                break;
            case 2:
                RedSpyAnalysis<2, readBufferSlotIndex>::CheckNByteValueAfterWrite(opAddr, drcontext, cur_ctxt_hndl, memOp);
                break;
            case 4:
                RedSpyAnalysis<4, readBufferSlotIndex>::CheckNByteValueAfterWrite(opAddr, drcontext, cur_ctxt_hndl, memOp);
                break;
            case 8:
                RedSpyAnalysis<8, readBufferSlotIndex>::CheckNByteValueAfterWrite(opAddr, drcontext,  cur_ctxt_hndl, memOp);
                break;
            case 10:
                RedSpyAnalysis<10, readBufferSlotIndex>::CheckNByteValueAfterWrite(opAddr, drcontext, cur_ctxt_hndl, memOp);
                break;
            case 16:
                RedSpyAnalysis<16, readBufferSlotIndex>::CheckNByteValueAfterWrite(opAddr, drcontext, cur_ctxt_hndl, memOp);
                break;
            default:
                // TODO
                // CheckAfterLargeWrite();
                break;
        }
    }

    /*static void InstrumentReadValueBeforeAndAfterWriting(void *addr, void *drcontext, context_handle_t cur_ctxt_hndl, uint32_t refSize, uint32_t whichOp){
        //uint32_t refSize = ref->size;
        //dr_fprintf(gTraceFile, "whiOp = %d\n", whichOp);
        //void *tmp;
        //tmp = &whichOp;
        //dr_fprintf(gTraceFile, "tmp = %p\n", tmp);
        switch(refSize) {
            HANDLE_CASE(1, readBufferSlotIndex);
            #define HANDLE_CASE(NUM, BUFFER_INDEX)
            case(NUM): {RedSpyAnalysis<(NUM), (BUFFER_INDEX)>::RecordNByteValueBeforeWrite(addr, drcontext);
            RedSpyAnalysis<(NUM), (BUFFER_INDEX)>::CheckNByteValueAfterWrite(drcontext, cur_ctxt_hndl); } break 

            HANDLE_CASE(2, readBufferSlotIndex);
            HANDLE_CASE(4, readBufferSlotIndex);
            HANDLE_CASE(8, readBufferSlotIndex);
            HANDLE_CASE(10, readBufferSlotIndex);
            HANDLE_CASE(16, readBufferSlotIndex);
            default: {
                //RecordValueBeforeLargeWrite();
                //CheckAfterLargeWrite();
            }
        }
    }*/

};


// client want to do
void
BeforeWrite(void *drcontext, context_handle_t cur_ctxt_hndl, mem_ref_t *ref, int32_t num, int32_t num_write)
{
    // add online analysis here
    //dr_fprintf(gTraceFile, "Before function: num_write = %d\n", num_write);
    int readBufferSlotIndex = 0;
    for(int32_t memOp = 0; memOp < num_write; memOp++){
        //dr_fprintf(gTraceFile, "readBufferSlotIndex = %d\n", readBufferSlotIndex);
        //dr_fprintf(gTraceFile, "memOp = %d\n", memOp);
        switch(readBufferSlotIndex){
            case 0:
                // Read the value at location before this instruction
                RedSpyInstrument<0>::InstrumentValueBeforeWriting(drcontext, cur_ctxt_hndl, ref, memOp);
                //RedSpyInstrument<0>::InstrumentReadValueBeforeAndAfterWriting(addr, drcontext, cur_ctxt_hndl, refSize, memOp);
                //dr_fprintf(gTraceFile, "Case 0\n");
                break;
            case 1:
                RedSpyInstrument<1>::InstrumentValueBeforeWriting(drcontext, cur_ctxt_hndl, ref, memOp);
                //RedSpyInstrument<1>::InstrumentReadValueBeforeAndAfterWriting(addr, drcontext, cur_ctxt_hndl, refSize, memOp);
                //dr_fprintf(gTraceFile, "Case 1\n");
                break;
            case 2:
                RedSpyInstrument<2>::InstrumentValueBeforeWriting(drcontext, cur_ctxt_hndl, ref, memOp);
                //RedSpyInstrument<2>::InstrumentReadValueBeforeAndAfterWriting(addr, drcontext, cur_ctxt_hndl, refSize, memOp);
                //dr_fprintf(gTraceFile, "Case 2\n");
                break;
            case 3:
                RedSpyInstrument<3>::InstrumentValueBeforeWriting(drcontext, cur_ctxt_hndl, ref, memOp);
                //RedSpyInstrument<3>::InstrumentReadValueBeforeAndAfterWriting(addr, drcontext, cur_ctxt_hndl, refSize, memOp);
                //dr_fprintf(gTraceFile, "Case 3\n");
                break;
            case 4:
                RedSpyInstrument<4>::InstrumentValueBeforeWriting(drcontext, cur_ctxt_hndl, ref, memOp);
                //RedSpyInstrument<4>::InstrumentReadValueBeforeAndAfterWriting(addr, drcontext, cur_ctxt_hndl, refSize, memOp);
                //dr_fprintf(gTraceFile, "Case 4\n");
                break;
            default:
                //assert(0 && "NYI");
                break;
        }
        // use next slot for the next write operand
        readBufferSlotIndex++;   
    }
}

void
AfterWrite(void *drcontext, context_handle_t cur_ctxt_hndl, op_ref *opList, int32_t num, int32_t num_write){
    //dr_fprintf(gTraceFile, "Run afterwrite\n");
    //void *opAddr = opList->opAddr;
    //uint32_t opSize = opList->opSize;
    //dr_fprintf(gTraceFile, "3: opAddr = %p\n", addr);
    //dr_fprintf(gTraceFile, "3: opSize = %lu\n", opSize);
    //dr_fprintf(gTraceFile, "Before function: num_write = %d\n", num_write);
    int readBufferSlotIndex = 0;
    dr_fprintf(gTraceFile, "num_write = %d\n", num_write);
    for(int32_t memOp = 0; memOp < num_write; memOp++){
        // read the value at this location after write
        switch(readBufferSlotIndex){
            case 0:
                //dr_fprintf(gTraceFile, "case 0\n");
                RedSpyInstrument<0>::InstrumentValueAfterWriting(drcontext, cur_ctxt_hndl, opList, memOp);
                break;
            case 1:
                //dr_fprintf(gTraceFile, "case 1\n");
                RedSpyInstrument<1>::InstrumentValueAfterWriting(drcontext, cur_ctxt_hndl, opList, memOp);
                break;
            case 2:
                //dr_fprintf(gTraceFile, "case 2\n");
                RedSpyInstrument<2>::InstrumentValueAfterWriting(drcontext, cur_ctxt_hndl, opList, memOp);
                break;
            case 3:
                //dr_fprintf(gTraceFile, "case 3\n");
                RedSpyInstrument<3>::InstrumentValueAfterWriting(drcontext, cur_ctxt_hndl, opList, memOp);
                break;
            case 4:
                //dr_fprintf(gTraceFile, "case 4\n");
                RedSpyInstrument<4>::InstrumentValueAfterWriting(drcontext, cur_ctxt_hndl, opList, memOp);
                break;
            default:
                //dr_fprintf(gTraceFile, "Run default\n");
                break;
        }
        // use next slot for the next write op
        readBufferSlotIndex++;
    }
}

// dr clean call
void
InsertCleancall(int32_t slot, int32_t num, int32_t num_read, int32_t num_write, int32_t op)
{
    void *drcontext = dr_get_current_drcontext();
    per_thread_t *pt = (per_thread_t *)drmgr_get_tls_field(drcontext, tls_idx);
    context_handle_t cur_ctxt_hndl = drcctlib_get_context_handle(drcontext, slot);

    // change the order of for loop and if condition
    for (int i = 0; i < memOp_num; i++){
        if(pt->opList[i].opAddr != 0) {
            AfterWrite(drcontext, cur_ctxt_hndl, &pt->opList[i], num, num_write);
        }
    }
    for (int i = 0; i < num; i++) {
        //uint64_t op = pt->opList[i];
        //dr_fprintf(gTraceFile, "opList[i] = %p\n", op);
        if (pt->cur_buf_list[i].addr != 0) {
            //void *opAddr = (&pt->cur_buf_list[i])->addr;
            // store addr and size of write ops in opList
            pt->opList[i].opAddr = (uint64_t*)((&pt->cur_buf_list[i])->addr);
            pt->opList[i].opSize = (uint32_t)((&pt->cur_buf_list[i])->size);
            //dr_fprintf(gTraceFile, "opList[i] = %p\n", pt->opList[i]);
            //dr_fprintf(gTraceFile, "1: addr = %p\n", (&pt->cur_buf_list[i])->addr);
            //dr_fprintf(gTraceFile, "2. opList[i].opAddr = %p\n", pt->opList[i].opAddr);
            //dr_fprintf(gTraceFile, "1: opSize = %lu\n", (&pt->cur_buf_list[i])->size);
            //dr_fprintf(gTraceFile, "2. opSize = %lu\n", pt->opList[i].opSize);
            BeforeWrite(drcontext, cur_ctxt_hndl, &pt->cur_buf_list[i], num, num_write);
        } else {
            pt->opList[i].opAddr = 0;
            pt->opList[i].opSize = 0;
        }
    }
    memOp_num = num;
    BUF_PTR(pt->cur_buf, mem_ref_t, INSTRACE_TLS_OFFS_BUF_PTR) = pt->cur_buf_list;
}

// insert
static void
InstrumentMem(void *drcontext, instrlist_t *ilist, instr_t *where, opnd_t ref)
{
    /* We need two scratch registers */
    reg_id_t reg_mem_ref_ptr, free_reg;
    if (drreg_reserve_register(drcontext, ilist, where, NULL, &reg_mem_ref_ptr) !=
            DRREG_SUCCESS ||
        drreg_reserve_register(drcontext, ilist, where, NULL, &free_reg) !=
            DRREG_SUCCESS) {
        DRCCTLIB_EXIT_PROCESS("InstrumentMem drreg_reserve_register != DRREG_SUCCESS");
    }
    if (!drutil_insert_get_mem_addr(drcontext, ilist, where, ref, free_reg,
                                    reg_mem_ref_ptr)) {
        MINSERT(ilist, where,
                XINST_CREATE_load_int(drcontext, opnd_create_reg(free_reg),
                                      OPND_CREATE_CCT_INT(0)));
    }
    dr_insert_read_raw_tls(drcontext, ilist, where, tls_seg,
                           tls_offs + INSTRACE_TLS_OFFS_BUF_PTR, reg_mem_ref_ptr);
    // store mem_ref_t->addr
    MINSERT(ilist, where,
            XINST_CREATE_store(
                drcontext, OPND_CREATE_MEMPTR(reg_mem_ref_ptr, offsetof(mem_ref_t, addr)),
                opnd_create_reg(free_reg)));

    // store mem_ref_t->size
/*
#ifdef ARM_CCTLIB
    MINSERT(ilist, where,
            XINST_CREATE_load_int(drcontext, opnd_create_reg(free_reg),
                                  OPND_CREATE_CCT_INT(drutil_opnd_mem_size_in_bytes(ref, where))));
    MINSERT(ilist, where,
            XINST_CREATE_store(drcontext, OPND_CREATE_MEMPTR(reg_mem_ref_ptr, offsetof(mem_ref_t, size)),
                             opnd_create_reg(free_reg)));
#else
    MINSERT(ilist, where,
            XINST_CREATE_store(drcontext, OPND_CREATE_MEMPTR(reg_mem_ref_ptr, offsetof(mem_ref_t, size)),
                             OPND_CREATE_CCT_INT(drutil_opnd_mem_size_in_bytes(ref, where))));
#endif
*/
    // store mem_ref_t->size
    MINSERT(ilist, where,
            XINST_CREATE_load_int(drcontext, opnd_create_reg(free_reg),
                                  OPND_CREATE_CCT_INT(drutil_opnd_mem_size_in_bytes(ref, where))));
    MINSERT(ilist, where,
            XINST_CREATE_store(drcontext, OPND_CREATE_MEMPTR(reg_mem_ref_ptr, offsetof(mem_ref_t, size)),
                             opnd_create_reg(free_reg)));

#ifdef ARM_CCTLIB
    MINSERT(ilist, where,
            XINST_CREATE_load_int(drcontext, opnd_create_reg(free_reg),
                                  OPND_CREATE_CCT_INT(sizeof(mem_ref_t))));
    MINSERT(ilist, where,
            XINST_CREATE_add(drcontext, opnd_create_reg(reg_mem_ref_ptr),
                             opnd_create_reg(free_reg)));
#else
    MINSERT(ilist, where,
            XINST_CREATE_add(drcontext, opnd_create_reg(reg_mem_ref_ptr),
                             OPND_CREATE_CCT_INT(sizeof(mem_ref_t))));
#endif
    dr_insert_write_raw_tls(drcontext, ilist, where, tls_seg,
                            tls_offs + INSTRACE_TLS_OFFS_BUF_PTR, reg_mem_ref_ptr);
    /* Restore scratch registers */
    if (drreg_unreserve_register(drcontext, ilist, where, reg_mem_ref_ptr) !=
            DRREG_SUCCESS ||
        drreg_unreserve_register(drcontext, ilist, where, free_reg) != DRREG_SUCCESS) {
        DRCCTLIB_EXIT_PROCESS("InstrumentMem drreg_unreserve_register != DRREG_SUCCESS");
    }
}

// analysis
void
InstrumentInsCallback(void *drcontext, instr_instrument_msg_t *instrument_msg)
{

    instrlist_t *bb = instrument_msg->bb;
    instr_t *instr = instrument_msg->instr;
    int32_t slot = instrument_msg->slot;

#ifdef x86_CCTLIB
    if (drreg_reserve_aflags(drcontext, bb, instr) != DRREG_SUCCESS) {
        DRCCTLIB_EXIT_PROCESS("instrument_before_every_instr_meta_instr "
                              "drreg_reserve_aflags != DRREG_SUCCESS");
    }
#endif

    int num = 0;
    int num_read = 0;
    int num_write = 0;
    int op = 0; //read is 0, write is 1

    /*for (int i = 0; i < instr_num_srcs(instr); i++) {
        if (opnd_is_memory_reference(instr_get_src(instr, i))) { //src = read
            num++;
            num_read++;
            InstrumentMem(drcontext, bb, instr, instr_get_src(instr, i));
        }
    }
    dr_insert_clean_call(drcontext, bb, instr, (void *)InsertCleancall, false, 5,
                         OPND_CREATE_CCT_INT(slot), OPND_CREATE_CCT_INT(num), OPND_CREATE_CCT_INT(num_read), OPND_CREATE_CCT_INT(num_write), OPND_CREATE_CCT_INT(op));
    */

    for (int i = 0; i < instr_num_dsts(instr); i++) {
        if (opnd_is_memory_reference(instr_get_dst(instr, i))) { //dst = write
            num++;
            num_write++;
            op = 1;
            InstrumentMem(drcontext, bb, instr, instr_get_dst(instr, i));
        }
    }
#ifdef x86_CCTLIB
    if (drreg_unreserve_aflags(drcontext, bb, instr) != DRREG_SUCCESS) {
        DRCCTLIB_EXIT_PROCESS("drreg_unreserve_aflags != DRREG_SUCCESS");
    }
#endif

    // when num_write == 0?
    // if (num_write == 0)
    //     return;
    dr_insert_clean_call(drcontext, bb, instr, (void *)InsertCleancall, false, 5,
                         OPND_CREATE_CCT_INT(slot), OPND_CREATE_CCT_INT(num), OPND_CREATE_CCT_INT(num_read), OPND_CREATE_CCT_INT(num_write), OPND_CREATE_CCT_INT(op));
}

static void
InitThreadData(RedSpyThreadData *tdata){
    tdata->bytesWritten = 0;
}

static void
ClientThreadStart(void *drcontext)
{
    per_thread_t *pt = (per_thread_t *)dr_thread_alloc(drcontext, sizeof(per_thread_t));
    if (pt == NULL) {
        DRCCTLIB_EXIT_PROCESS("pt == NULL");
    }
    drmgr_set_tls_field(drcontext, tls_idx, (void *)pt);

    pt->cur_buf = dr_get_dr_segment_base(tls_seg);
    pt->cur_buf_list =
        (mem_ref_t *)dr_global_alloc(TLS_MEM_REF_BUFF_SIZE * sizeof(mem_ref_t));
    //pt->opList = dr_global_alloc(TLS_MEM_REF_BUFF_SIZE * sizeof(uint64_t));
    BUF_PTR(pt->cur_buf, mem_ref_t, INSTRACE_TLS_OFFS_BUF_PTR) = pt->cur_buf_list;

}

static void
ClientThreadEnd(void *drcontext)
{
    per_thread_t *pt = (per_thread_t *)drmgr_get_tls_field(drcontext, tls_idx);
    dr_global_free(pt->cur_buf_list, TLS_MEM_REF_BUFF_SIZE * sizeof(mem_ref_t));
    //dr_global_free(pt->opList, TLS_MEM_REF_BUFF_SIZE * sizeof(uint64_t));
    dr_thread_free(drcontext, pt, sizeof(per_thread_t));
}

static void
ClientInit(int argc, const char *argv[])
{
    char name[MAXIMUM_PATH] = "";
    DRCCTLIB_INIT_LOG_FILE_NAME(name, "test", "out");
    gTraceFile = dr_open_file(name, DR_FILE_WRITE_OVERWRITE | DR_FILE_ALLOW_LARGE);
    DR_ASSERT(gTraceFile != INVALID_FILE);
    dr_fprintf(gTraceFile, "ClientInit\n");
    
}

static void
ClientExit(void)
{
    // add output module here
    dr_fprintf(gTraceFile, "ClientExit\n");

    drcctlib_exit();

    if (!dr_raw_tls_cfree(tls_offs, INSTRACE_TLS_COUNT)) {
        DRCCTLIB_EXIT_PROCESS(
            "ERROR: drcctlib_memory_with_addr_and_refsize_clean_call dr_raw_tls_calloc fail");
    }
    if (!drmgr_unregister_thread_init_event(ClientThreadStart) ||
        !drmgr_unregister_thread_exit_event(ClientThreadEnd) ||
        !drmgr_unregister_tls_field(tls_idx)) {
        DRCCTLIB_PRINTF("ERROR: drcctlib_memory_with_addr_and_refsize_clean_call failed to "
                        "unregister in ClientExit");
    }
    drmgr_exit();
    if (drreg_exit() != DRREG_SUCCESS) {
        DRCCTLIB_PRINTF("failed to exit drreg");
    }
    drutil_exit();
}

#ifdef __cplusplus
extern "C" {
#endif

DR_EXPORT void
dr_client_main(client_id_t id, int argc, const char *argv[])
{
    dr_set_client_name("DynamoRIO Client 'drcctlib_memory_with_addr_and_refsize_clean_call'",
                       "http://dynamorio.org/issues");
    ClientInit(argc, argv);

    if (!drmgr_init()) {
        DRCCTLIB_EXIT_PROCESS("ERROR: drcctlib_memory_with_addr_and_refsize_clean_call "
                              "unable to initialize drmgr");
    }
    drreg_options_t ops = { sizeof(ops), 4 /*max slots needed*/, false };
    if (drreg_init(&ops) != DRREG_SUCCESS) {
        DRCCTLIB_EXIT_PROCESS("ERROR: drcctlib_memory_with_addr_and_refsize_clean_call "
                              "unable to initialize drreg");
    }
    if (!drutil_init()) {
        DRCCTLIB_EXIT_PROCESS("ERROR: drcctlib_memory_with_addr_and_refsize_clean_call "
                              "unable to initialize drutil");
    }
    drmgr_register_thread_init_event(ClientThreadStart);
    drmgr_register_thread_exit_event(ClientThreadEnd);

    tls_idx = drmgr_register_tls_field();
    if (tls_idx == -1) {
        DRCCTLIB_EXIT_PROCESS("ERROR: drcctlib_memory_with_addr_and_refsize_clean_call "
                              "drmgr_register_tls_field fail");
    }
    if (!dr_raw_tls_calloc(&tls_seg, &tls_offs, INSTRACE_TLS_COUNT, 0)) {
        DRCCTLIB_EXIT_PROCESS(
            "ERROR: drcctlib_memory_with_addr_and_refsize_clean_call dr_raw_tls_calloc fail");
    }
    drcctlib_init(DRCCTLIB_FILTER_MEM_ACCESS_INSTR, INVALID_FILE, InstrumentInsCallback, false);
    dr_register_exit_event(ClientExit);
}

#ifdef __cplusplus
}
#endif
