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
#include <algorithm>

#include "dr_api.h"
#include "drmgr.h"
#include "drreg.h"
#include "drutil.h"
#include "drcctlib.h"
#include "shadow_memory_ml.h"

using namespace std;

#define DRCCTLIB_PRINTF(_FORMAT, _ARGS...) \
    DRCCTLIB_PRINTF_TEMPLATE("memory_with_addr_and_refsize_clean_call", _FORMAT, ##_ARGS)
#define DRCCTLIB_EXIT_PROCESS(_FORMAT, _ARGS...)                                           \
    DRCCTLIB_CLIENT_EXIT_PROCESS_TEMPLATE("memory_with_addr_and_refsize_clean_call", _FORMAT, \
                                          ##_ARGS)

static int tls_idx;
static int memOp_num; 
// for register analysis
static uint64_t prev_ins;
static uint64_t cur_ins;
static uint32_t regID;
static uint32_t regSize;
static int regOp_num;

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
#define REG_MAX (100)

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

#define DECODE_DEAD(data) static_cast<context_handle_t>(((data) & 0xffffffffffffffff) >> 32)
#define DECODE_KILL(data) (static_cast<context_handle_t>( (data) & 0x00000000ffffffff))

#define MAX_CONTEXTS (50)

static file_t gTraceFile;
static uint8_t** gL1PageTable[LEVEL_1_PAGE_TABLE_SIZE];
static ConcurrentShadowMemoryMl<context_handle_t> sm;


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
#    ifdef CCTLIB_64
#        define OPND_CREATE_CCT_INT OPND_CREATE_INT64
#    else
#        define OPND_CREATE_CCT_INT OPND_CREATE_INT32
#    endif
#endif

typedef struct _mem_ref_t {
    app_pc addr;
    size_t size;
} mem_ref_t;

typedef struct op_ref{
    uint64_t *opAddr;
    uint32_t opSize;
}op_ref;

typedef struct reg_ref{
    uint64_t ins_ip;
    uint64_t register_id;
    uint32_t register_size;
    uint64_t register_value;
}reg_ref;

typedef struct _per_thread_t {
    mem_ref_t *cur_buf_list;
    void *cur_buf;
    op_ref opList[MAX_WRITE_OPS_IN_INS];
    //uint64_t opList[MAX_WRITE_OPS_IN_INS];
    reg_ref regInfo[REG_MAX];
    unordered_map<uint64_t, reg_ref> RegInfoMap;
    uint64_t value[MAX_WRITE_OPS_IN_INS];
    uint64_t bytesWritten;
} per_thread_t;

typedef struct RedanduncyData{
    context_handle_t dead;
    context_handle_t kill;
    uint64_t frequency;
} RedanduncyData;

void *lock;

static unordered_map<uint64_t, unordered_map<uint64_t, uint64_t>> RegisterMap;
static unordered_map<uint64_t, uint64_t> RedMap[THREAD_MAX];
//static unordered_map<int, unordered_map<uint64_t, uint64_t>> RedMap;

static void AddToRedTable(uint64_t key, uint16_t value, int threadID){
#ifdef MULTI_THREADED
    //LOCK_RED_MAP();
#endif
    unordered_map<uint64_t, uint64_t>::iterator it = RedMap[threadID].find(key);
    if (it == RedMap[threadID].end()) {
        RedMap[threadID][key] = value;
    } else {
        it->second += value;
        //dr_fprintf(gTraceFile, "RedTable->first = %llu, RedTable->second = %llu\n", it->first, it->second);
    }
#ifdef MULTI_THREADED
    //UNLOCK_RED_MAP();
#endif
}

template<int start, int end, int incr>
struct UnrolledLoop{
    static void Body(function<void (const int)> func){
        func(start); // Real loop body
        UnrolledLoop<start+incr, end, incr>::Body(func); //unroll next iteration
    }
};

template<int end, int incr>
struct UnrolledLoop<end, end, incr>{
    static void Body(function<void (const int)> func){
        // empty body
    }
};

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
        per_thread_t *pt = (per_thread_t *)drmgr_get_tls_field(drcontext, tls_idx);
        pt->bytesWritten += AccessLen;
        
        switch(AccessLen) {
            case 1: 
                uint8_t temp1;
                if (!dr_safe_read(addr, 1, &temp1, NULL))
                    return;
                *((uint8_t *)(&(pt->value[memOp]))) = temp1;
                break;
            case 2:
                uint16_t temp2;
                if (!dr_safe_read(addr, 2, &temp2, NULL))
                    return;
                *((uint16_t *)(&(pt->value[memOp]))) = temp2;
                break;
            case 4:
                uint32_t temp4;
                if (!dr_safe_read(addr, 4, &temp4, NULL))
                    return;
                *((uint32_t *)(&(pt->value[memOp]))) = temp4;
                break;
            case 8: 
                uint64_t temp8;
                if (!dr_safe_read(addr, 8, &temp8, NULL))
                    return;
                *((uint64_t *)(&(pt->value[memOp]))) = temp8;
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
                if (*((uint8_t *)(&(pt->value[memOp]))) == temp1){
                    isRedundantWrite = true;
                }
                break;
            }
            case 2:{
                uint16_t temp2;
                if (!dr_safe_read(opAddr, 2, &temp2, NULL))
                    return;
                if (*((uint16_t *)(&(pt->value[memOp]))) == temp2){
                    isRedundantWrite = true;
                }
                break;
            }
            case 4:{
                uint32_t temp4;
                if (!dr_safe_read(opAddr, 4, &temp4, NULL))
                    return;
                if (*((uint32_t *)(&(pt->value[memOp]))) == temp4){
                    isRedundantWrite = true;
                }
                break;
            }
            case 8:{
                // store the value of opAddr to temp8
                uint64_t temp8;
                if (!dr_safe_read(opAddr, 8, &temp8, NULL))
                    return;
                if (*((uint64_t *)(&(pt->value[memOp]))) == temp8){
                    isRedundantWrite = true;
                }
                break;
            }
            //default:
                //break;
        }
        uint8_t *status = GetOrCreateShadowBaseAddress((uint64_t)opAddr);
        //uint8_t *status = (uint8_t *) get<0>(sm.GetOrCreateShadowBaseAddress((uint64_t)opAddr));
        int threadID = drcctlib_get_thread_id();
        context_handle_t *prevIP = (context_handle_t*)(status + PAGE_OFFSET((uint64_t)opAddr) * sizeof(context_handle_t));
        bool isAccessWithinPageBoundary = IS_ACCESS_WITHIN_PAGE_BOUNDARY((uint64_t)opAddr, AccessLen);
        if (isRedundantWrite) {
            // redundancy detected
            if(isAccessWithinPageBoundary){
                // All from the same context ?
                if (UnrolledConjunction<0, AccessLen, 1>::Body( [&] (int index) -> bool {return (prevIP[index] == prevIP[0]); } )) {
                    // repory to RedTable
                    AddToRedTable(MAKE_CONTEXT_PAIR(prevIP[0], cur_ctxt_hndl), AccessLen, threadID);
                    // update context
                    UnrolledLoop<0, AccessLen, 1>::Body( [&] (int index) -> void {
                        // update context
                        prevIP[index] = cur_ctxt_hndl;
                    });
                } else {
                    // different contexts
                    UnrolledLoop<0, AccessLen, 1>::Body( [&] (int index) -> void {
                        // report in RedTable
                        AddToRedTable(MAKE_CONTEXT_PAIR(prevIP[index], cur_ctxt_hndl), 1, threadID);
                        // update context
                        prevIP[index] = cur_ctxt_hndl;
                    });
                }
            } else {
                // write across a 64k page boundary
                // first byte is on this page though
                AddToRedTable(MAKE_CONTEXT_PAIR(prevIP[0], cur_ctxt_hndl), 1, threadID);
                // update context
                prevIP[0] = cur_ctxt_hndl;
                // remaining bytes (from 1 to AccessLen) across a 64k page boundary
                UnrolledLoop<1, AccessLen, 1>::Body( [&] (int index) -> void {
                    status = GetOrCreateShadowBaseAddress((uint64_t)opAddr + index);
                    //status = get<0>(sm.GetOrCreateShadowBaseAddress((uint64_t)opAddr + index));
                    prevIP = (context_handle_t*)(status + PAGE_OFFSET(((uint64_t)opAddr + index)) * sizeof(context_handle_t));
                    // report in RedTable
                    AddToRedTable(MAKE_CONTEXT_PAIR(prevIP[0], cur_ctxt_hndl), 1, threadID);
                    // update context
                    prevIP[0] = cur_ctxt_hndl;
                });
            }
        } else {
            // no redundancy, just update context
            if (isAccessWithinPageBoundary) {
                UnrolledLoop<0, AccessLen, 1>::Body( [&] (int index) -> void {
                    // all from the same context
                    // update context
                    prevIP[index] = cur_ctxt_hndl;
                });
            } else {
                // write across a 64k page boundary
                UnrolledLoop<0, AccessLen, 1>::Body( [&] (int index) -> void {
                    status = GetOrCreateShadowBaseAddress((uint64_t)opAddr + index);
                    //status = get<0>(sm.GetOrCreateShadowBaseAddress((uint64_t)opAddr + index))
                    prevIP = (context_handle_t*)(status + PAGE_OFFSET(((uint64_t)opAddr + index)) * sizeof(context_handle_t));
                    // update context
                    prevIP[0] = cur_ctxt_hndl;
                });
            }
        }
    }
};

template<uint32_t readBufferSlotIndex>
struct RedSpyInstrument{
    static void InstrumentValueBeforeWriting(void *drcontext, context_handle_t cur_ctxt_hndl, mem_ref_t *ref, uint32_t memOp){
        // get address and size of memOp
        void *addr = ref->addr;
        uint32_t refSize = ref->size;
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
};


// client want to do
void
BeforeWrite(void *drcontext, context_handle_t cur_ctxt_hndl, mem_ref_t *ref, int32_t num, int32_t num_write)
{
    int readBufferSlotIndex = 0;
    for(int32_t memOp = 0; memOp < num_write; memOp++){
        switch(readBufferSlotIndex){
            case 0:
                // Read the value at location before this instruction
                RedSpyInstrument<0>::InstrumentValueBeforeWriting(drcontext, cur_ctxt_hndl, ref, memOp);
                break;
            case 1:
                RedSpyInstrument<1>::InstrumentValueBeforeWriting(drcontext, cur_ctxt_hndl, ref, memOp);
                break;
            case 2:
                RedSpyInstrument<2>::InstrumentValueBeforeWriting(drcontext, cur_ctxt_hndl, ref, memOp);
                break;
            case 3:
                RedSpyInstrument<3>::InstrumentValueBeforeWriting(drcontext, cur_ctxt_hndl, ref, memOp);
                break;
            case 4:
                RedSpyInstrument<4>::InstrumentValueBeforeWriting(drcontext, cur_ctxt_hndl, ref, memOp);
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
    int readBufferSlotIndex = 0;
    for(int32_t memOp = 0; memOp < num_write; memOp++){
        // read the value at this location after write
        switch(readBufferSlotIndex){
            case 0:
                RedSpyInstrument<0>::InstrumentValueAfterWriting(drcontext, cur_ctxt_hndl, opList, memOp);
                break;
            case 1:
                RedSpyInstrument<1>::InstrumentValueAfterWriting(drcontext, cur_ctxt_hndl, opList, memOp);
                break;
            case 2:
                RedSpyInstrument<2>::InstrumentValueAfterWriting(drcontext, cur_ctxt_hndl, opList, memOp);
                break;
            case 3:
                RedSpyInstrument<3>::InstrumentValueAfterWriting(drcontext, cur_ctxt_hndl, opList, memOp);
                break;
            case 4:
                RedSpyInstrument<4>::InstrumentValueAfterWriting(drcontext, cur_ctxt_hndl, opList, memOp);
                break;
            default:
                break;
        }
        // use next slot for the next write op
        readBufferSlotIndex++;
    }
}

// dr clean call
void
InsertCleancall(int32_t slot, int32_t num, int32_t num_write)
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
        if (pt->cur_buf_list[i].addr != 0) {
            // store the addr and size of ops in opList
            // check the values in addr after running ins
            pt->opList[i].opAddr = (uint64_t*)((&pt->cur_buf_list[i])->addr);
            pt->opList[i].opSize = (uint32_t)((&pt->cur_buf_list[i])->size);
            BeforeWrite(drcontext, cur_ctxt_hndl, &pt->cur_buf_list[i], num, num_write);
        } else {
            pt->opList[i].opAddr = 0;
            pt->opList[i].opSize = 0;
        }
    }
    memOp_num = num;
    BUF_PTR(pt->cur_buf, mem_ref_t, INSTRACE_TLS_OFFS_BUF_PTR) = pt->cur_buf_list;
}

void
InsertCleancallReg(int32_t slot, int num_reg, uint64_t cur_ins, uint32_t regSize, uint32_t regID) {
    void *drcontext = dr_get_current_drcontext();
    per_thread_t *pt = (per_thread_t *)drmgr_get_tls_field(drcontext, tls_idx);
    context_handle_t cur_ctxt_hndl = drcctlib_get_context_handle(drcontext, slot);
    dr_mcontext_t mc = {sizeof(mc), DR_MC_ALL};
    dr_get_mcontext(drcontext, &mc);

    //int threadID = drcctlib_get_thread_id();
    if (num_reg != 0) {
        dr_fprintf(gTraceFile, "reg size = %lu\n", regSize);
        dr_fprintf(gTraceFile, "reg id = %lu\n", regID);
        dr_fprintf(gTraceFile, "num_reg = %d\n", num_reg);
    }
    for (int i = 0; i < regOp_num; i++) {
        if (pt->regInfo[i].register_value != 0) {
            
            if (regSize == 4) {
                uint32_t reg_value = (uint32_t)reg_get_value(regID, &mc);
                if (pt->regInfo[i].register_value == reg_value) {
                    dr_fprintf(gTraceFile, "value equal\n");
                }
            }

            if (regID == pt->regInfo[i].register_id) {
                dr_fprintf(gTraceFile, "id equal\n");
                
                
                /*if (regSize == 4) {
                    if ((uint32_t)reg_get_value(regID, &mc) == pt->regInfo[i].register_value) {
                        dr_fprintf(gTraceFile, "4: equal\n");
                        // Add to RedMap
                    } else {
                        // update ctxt
                    }
                }
                if (regSize == 8) {
                    if (reg_get_value(regID, &mc) == pt->regInfo[i].register_value) {
                        dr_fprintf(gTraceFile, "8: equal\n");
                        // Add to RedMap
                    } else {
                        // update ctxt
                    }
                }*/
            }

            
            
        }
    }

    for (int i = 0; i < num_reg; i++) {
        // store reg info in RegisterMap
        if (regSize == 4) {
            uint32_t reg_value = (uint32_t)reg_get_value(regID, &mc);
            //dr_fprintf(gTraceFile, "4: register value is: %lu\n", reg_value);
            //RegisterMap[prev_ins][regID] = reg_value;
            //dr_fprintf(gTraceFile, "Print Map: %lu\n", RegisterMap[prev_ins][regID]);
            pt->regInfo[i].register_value = reg_value;
            pt->regInfo[i].register_id = regID;
            //pt->regInfo[i].ins_ip = cur_ins;
        } else {
            uint64_t reg_value = reg_get_value(regID, &mc);
            //dr_fprintf(gTraceFile, "8: register value is: %llu\n", reg_value);
            //RegisterMap[prev_ins][regID] = reg_value;
            //dr_fprintf(gTraceFile, "Print Map: %llu\n", RegisterMap[prev_ins][regID]);
            pt->regInfo[i].register_value = reg_value;
            pt->regInfo[i].register_id = regID;
        }
    }
    regOp_num = num_reg;
    
    prev_ins = cur_ins;

    /*
    if (RegisterMap[cur_ins] == RegisterMap[prev_ins]) {
        //dr_fprintf(gTraceFile, "is equal\n");
        AddToRedTable(MAKE_CONTEXT_PAIR(pt->regCtxt[regID], cur_ctxt_hndl), regSize, threadID);
    } else {
        // TODO
        pt->regCtxt[regID] = cur_ctxt_hndl;
    }*/
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
    int num_write = 0;
    int num_reg = 0;

    // register analysis
    dr_fprintf(gTraceFile, "******************** instr starts \n");
    cur_ins = (uint64_t)instr_get_app_pc(instr);
    dr_fprintf(gTraceFile, "cur ins = %llu\n", cur_ins);
    //dr_fprintf(gTraceFile, "prev ins = %llu\n", prev_ins);
    //dr_fprintf(gTraceFile, "ins ip: %llu\n", reg_ip);
    for (int i = 0; i < instr_num_dsts(instr); i++) {
        // if op is a register operand
        if (opnd_is_reg(instr_get_dst(instr, i))) {
            num_reg++;
            opnd_t op_reg = instr_get_dst(instr, i);
            uint32_t reg_id = (uint64_t)opnd_get_reg(op_reg);
            regID = reg_id;
            regSize = (uint32_t)reg_get_bits(reg_id);
            //dr_fprintf(gTraceFile, "reg id = %lu\n", reg_id);
            dr_fprintf(gTraceFile, "reg size = %lu\n", regSize);
            // const char *reg_name = get_register_name(reg_id);
            if (reg_is_gpr(reg_id)) {
                // 
            }
        }
    }
    dr_insert_clean_call(drcontext, bb, instr, (void *)InsertCleancallReg, false, 5,
                         OPND_CREATE_CCT_INT(slot), OPND_CREATE_CCT_INT(num_reg), OPND_CREATE_CCT_INT(cur_ins), OPND_CREATE_CCT_INT(regSize), OPND_CREATE_CCT_INT(regID));                    
    //prev_ins = cur_ins;


    for (int i = 0; i < instr_num_dsts(instr); i++) {
        if (opnd_is_memory_reference(instr_get_dst(instr, i))) { //dst = write
            num++;
            num_write++;
            //op = 1;
            InstrumentMem(drcontext, bb, instr, instr_get_dst(instr, i));
        }
    }
#ifdef x86_CCTLIB
    if (drreg_unreserve_aflags(drcontext, bb, instr) != DRREG_SUCCESS) {
        DRCCTLIB_EXIT_PROCESS("drreg_unreserve_aflags != DRREG_SUCCESS");
    }
#endif

    dr_insert_clean_call(drcontext, bb, instr, (void *)InsertCleancall, false, 3,
                         OPND_CREATE_CCT_INT(slot), OPND_CREATE_CCT_INT(num), OPND_CREATE_CCT_INT(num_write));
}


static bool RedundancyCompare(const struct RedanduncyData &first, const struct RedanduncyData &second) {
    return first.frequency > second.frequency ? true : false;
}

void PrintRedundancyPairs(void * drcontext,int threadID) {
    vector<RedanduncyData> tmpList;
    vector<RedanduncyData>::iterator tmpIt;
    uint64_t grandTotalRedundantBytes = 0;
    dr_fprintf(gTraceFile, "********** Dump Data from Thread %d **********\n", threadID);
    for (unordered_map<uint64_t, uint64_t>::iterator it = RedMap[threadID].begin(); it != RedMap[threadID].end(); it++) {
        //dr_fprintf(gTraceFile, "key in map = %llu\n", (*it).first);
        context_handle_t dead = DECODE_DEAD((*it).first);
        context_handle_t kill = DECODE_KILL((*it).first);
        //dr_fprintf(gTraceFile, "dead data: %lu, and kill data: %lu\n", dead, kill);

        for (tmpIt = tmpList.begin(); tmpIt != tmpList.end(); tmpIt++) {
            bool ct1 = false;
            if (dead == 0 || ((*tmpIt).dead) == 0) {
                if (dead == 0 && ((*tmpIt).dead) == 0) 
                    ct1 = true;
            } else {
                ct1 = drcctlib_have_same_source_line(dead, (*tmpIt).dead);
            }
            bool ct2 = drcctlib_have_same_source_line(kill, (*tmpIt).kill);
            if (ct1 && ct2) {
                (*tmpIt).frequency += (*it).second;
                grandTotalRedundantBytes += (*it).second;
                break;
            }
        }
        if (tmpIt == tmpList.end()) {
            RedanduncyData tmp = { dead, kill, (*it).second};
            tmpList.push_back(tmp);
            grandTotalRedundantBytes += tmp.frequency;
        }
    }
    per_thread_t *pt = (per_thread_t *)drmgr_get_tls_field(drcontext, tls_idx);
    dr_fprintf(gTraceFile, "\nTotal redundant bytes = %f %%\n", grandTotalRedundantBytes * 100.0 / (pt->bytesWritten));

    sort(tmpList.begin(), tmpList.end(), RedundancyCompare);
    vector<RedanduncyData>::iterator listIt;
    int cntxNum = 0;
    for (listIt = tmpList.begin(); listIt != tmpList.end(); listIt++) {
        if (cntxNum < MAX_CONTEXTS) {
            dr_fprintf(gTraceFile, "\n========== (%f) %% ==========\n", (*listIt).frequency * 100.0 / grandTotalRedundantBytes);
            if ((*listIt).dead == 0) {
                dr_fprintf(gTraceFile, "\nPrepopulated with by OS\n");
            } else {
                //drcctlib_print_full_cct(gTraceFile, (*listIt).dead, true, false, -1);
                drcctlib_print_backtrace(gTraceFile, (*listIt).dead, false, true, -1);
                dr_fprintf(gTraceFile, "dead context: %lu\n", (*listIt).dead);
            }
            dr_fprintf(gTraceFile, "--------------------Redundantly written by--------------------\n");
            drcctlib_print_backtrace(gTraceFile, (*listIt).kill, false, true, -1);
            dr_fprintf(gTraceFile, "kill context: %lu\n", (*listIt).kill);
        }
        else {
            break;
        }
        cntxNum++;
    }
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
    BUF_PTR(pt->cur_buf, mem_ref_t, INSTRACE_TLS_OFFS_BUF_PTR) = pt->cur_buf_list;

}

static void
ClientThreadEnd(void *drcontext)
{
    per_thread_t *pt = (per_thread_t *)drmgr_get_tls_field(drcontext, tls_idx);
    dr_global_free(pt->cur_buf_list, TLS_MEM_REF_BUFF_SIZE * sizeof(mem_ref_t));
    dr_thread_free(drcontext, pt, sizeof(per_thread_t));

    int threadID = drcctlib_get_thread_id();
    
    // need lock for drcctlib_have_same_source_line
    dr_mutex_lock(lock);
    PrintRedundancyPairs(drcontext, threadID);
    dr_mutex_unlock(lock);
    // clear the map
    RedMap[threadID].clear();
}

static void
ClientInit(int argc, const char *argv[])
{
    char name[MAXIMUM_PATH] = "";
    DRCCTLIB_INIT_LOG_FILE_NAME(name, "redtemp", "out");
    gTraceFile = dr_open_file(name, DR_FILE_WRITE_OVERWRITE | DR_FILE_ALLOW_LARGE);
    DR_ASSERT(gTraceFile != INVALID_FILE);
    dr_fprintf(gTraceFile, "ClientInit\n");
    lock = dr_mutex_create();
    
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
    dr_mutex_destroy(lock);
}


bool
CustomFilter(instr_t *instr)
{
    return (instr_writes_memory(instr));
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
    drcctlib_init(CustomFilter, INVALID_FILE, InstrumentInsCallback, false);
    // drcctlib_init(DRCCTLIB_FILTER_MEM_ACCESS_INSTR, INVALID_FILE, InstrumentInsCallback, false);
    // add print function
    dr_register_exit_event(ClientExit);
}

#ifdef __cplusplus
}
#endif
