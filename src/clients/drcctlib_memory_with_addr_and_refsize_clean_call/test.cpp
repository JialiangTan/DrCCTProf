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
#include "drcctlib_vscodeex_format.h"

using namespace std;
using namespace DrCCTProf;

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

// #define TLS_MEM_REF_BUFF_SIZE 4096
#define TLS_MEM_REF_BUFF_SIZE 100
#define WINDOW_ENABLE 1000000
#define WINDOW_DISABLE 1000000000
#define TOP_REACH_NUM_SHOW 200
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

#define DECODE_DEAD(data) static_cast<context_handle_t>(((data) & 0xffffffffffffffff) >> 32)
#define DECODE_KILL(data) (static_cast<context_handle_t>( (data) & 0x00000000ffffffff))

#define MAX_CONTEXTS (50)


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
    aligned_ctxt_hndl_t ctxt_hndl;
    app_pc addr;
    size_t size;
    uint64_t value;
    // size of stored value
    uint64_t value_size;
} mem_ref_t;

typedef struct op_ref{
    uint64_t *opAddr;
    uint32_t opSize;
}op_ref;

typedef struct _per_thread_t {
    uint64_t last_bb_mem_ref_num;
    uint64_t last_mem_idx;
    uint64_t cur_mem_idx;
    int32_t cur_buf_fill_num;
    mem_ref_t *cur_buf_list;
    void *cur_buf;
    op_ref opList[MAX_WRITE_OPS_IN_INS];
    //uint64_t opList[MAX_WRITE_OPS_IN_INS];
    uint64_t value[MAX_WRITE_OPS_IN_INS];
    uint64_t bytesWritten;
} per_thread_t;

typedef struct RedanduncyData{
    context_handle_t dead;
    context_handle_t kill;
    uint64_t frequency;
} RedanduncyData;

void *lock;

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
    static inline void Body(function<void (const int)> func){
        func(start); // Real loop body
        UnrolledLoop<start+incr, end, incr>::Body(func); //unroll next iteration
    }
};

template<int end, int incr>
struct UnrolledLoop<end, end, incr>{
    static inline void Body(function<void (const int)> func){
        // empty body
    }
};

template<int start, int end, int incr>
struct UnrolledConjunction{
    static inline bool Body(function<bool (const int)> func){
        return func(start) && UnrolledConjunction<start+incr, end, incr>::Body(func); // unroll next iteration
    }
};

template<int end, int incr>
struct UnrolledConjunction<end, end, incr>{
    static inline bool Body(function<void (const int)> func){
        return true;
    }
};

// helper functions for shadow memory
static uint8_t* 
GetOrCreateShadowBaseAddress(uint64_t addr){
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


// certain FP instructions should not be approximated
static inline bool 
IsOkToApproximate(instr_t* instr) {
    int op = instr_get_opcode(instr);
    switch(op) {
        case OP_fldenv: //XED_ICLASS_FLDENV:
        case OP_fnstenv: //XED_ICLASS_FNSTENV:
        case OP_fnsave: //XED_ICLASS_FNSAVE:
        case OP_fldcw: //XED_ICLASS_FLDCW:
        case OP_fnstcw: //XED_ICLASS_FNSTCW:
        case OP_fxrstor32: //XED_ICLASS_FXRSTOR:
        case OP_fxrstor64: //XED_ICLASS_FXRSTOR64:
        case OP_fxsave32: //XED_ICLASS_FXSAVE:
        case OP_fxsave64: //XED_ICLASS_FXSAVE64:
            return false;
        default:
            return true;
    }
}

static inline bool 
IsFloatInstructionAndOkToApproximate(instr_t* instr) {
    //OP_constant op = instr_get_opcode(&instr);
    if(instr_is_floating(instr)){
        int op = instr_get_opcode(instr);
        switch(op) {
            /* added in Intel Sandy Bridge */
            case OP_xgetbv:
            case OP_xsetbv:
            case OP_xsave32: 
            case OP_xrstor32: 
            case OP_xsaveopt32:
            case OP_fxsave64:
            case OP_fxrstor64: 
            case OP_xsave64: 
            case OP_xrstor64:
            case OP_xsaveopt64:
                dr_fprintf(gTraceFile, "\n Not recognized by instr_is_floatin op is %d\n", op);
                return false;
            default:
                return IsOkToApproximate(instr);
        }
    }
    else{
        return false;
    }
}

bool 
IsDoubleOrFloat (int opcode){
	return (opcode == OP_vblendmps || opcode == OP_vbroadcastf32x4 || opcode == OP_vbroadcastf32x8 || 
    opcode == OP_vcompressps || opcode == OP_vcvtps2qq || opcode == OP_vcvtps2udq || 
    opcode == OP_vcvtps2uqq || opcode == OP_vcvtqq2ps || opcode == OP_vcvtss2usi || 
    opcode == OP_vcvttps2qq || opcode == OP_vcvttps2udq || opcode == OP_vcvttps2uqq || 
    opcode == OP_vcvttss2usi || opcode == OP_vcvtudq2ps || opcode == OP_vcvtuqq2ps || 
    opcode == OP_vcvtusi2ss || opcode == OP_vexp2ps || opcode == OP_vexpandps || 
    opcode == OP_vextractf32x4 || opcode == OP_vextractf32x8 || opcode == OP_vfixupimmps || 
    opcode == OP_vfixupimmss || opcode == OP_vfpclassps || opcode == OP_vfpclassss || 
    opcode == OP_vgatherpf0dps || opcode == OP_vgatherpf0qps || opcode == OP_vgatherpf1dps || 
    opcode == OP_vgatherpf1qps || opcode == OP_vgetexpps || opcode == OP_vgetexpss || 
    opcode == OP_vgetmantps || opcode == OP_vgetmantss || opcode == OP_vinsertf32x4 || 
    opcode == OP_vinsertf32x8 || opcode == OP_vpermi2ps || opcode == OP_vpermt2ps || 
    opcode == OP_vrangeps || opcode == OP_vrangess || opcode == OP_vrcp14ps || 
    opcode == OP_vrcp14ss || opcode == OP_vrcp28ps || opcode == OP_vrcp28ss || 
    opcode == OP_vreduceps || opcode == OP_vreducess || opcode == OP_vrndscaleps || 
    opcode == OP_vrndscaless || opcode == OP_vrsqrt14ps || opcode == OP_vrsqrt14ss || 
    opcode == OP_vrsqrt28ps || opcode == OP_vrsqrt28ss || opcode == OP_vscalefps || 
    opcode == OP_vscalefss || opcode == OP_vscatterdps || opcode == OP_vscatterqps || 
    opcode == OP_vscatterpf0dps || opcode == OP_vscatterpf0qps || opcode == OP_vscatterpf1dps || 
    opcode == OP_vscatterpf1qps || opcode == OP_vshuff32x4 || opcode == OP_vbroadcastf32x2);	
}


template<uint16_t AccessLen, uint32_t bufferOffset>
struct RedSpyAnalysis{
    static inline void RecordNByteValueBeforeWrite(void *addr, void* drcontext, uint32_t memOp){
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
    
    static inline void CheckNByteValueAfterWrite(void* opAddr, void* drcontext, context_handle_t cur_ctxt_hndl, uint32_t memOp){
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
                    //dr_fprintf(gTraceFile, "in case 4, equal\n");
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
    static inline void InstrumentValueBeforeWriting(void *drcontext, context_handle_t cur_ctxt_hndl, mem_ref_t *ref, uint32_t memOp){
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
    static inline void InstrumentValueAfterWriting(void *drcontext, context_handle_t cur_ctxt_hndl, op_ref *opList, uint32_t memOp){
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

bool
CustomFilter(instr_t *instr)
{
    return (instr_writes_memory(instr));
}


// dr clean call
void
InsertCleancall(int32_t slot, int32_t num, int32_t num_write)
{
    void *drcontext = dr_get_current_drcontext();
    per_thread_t *pt = (per_thread_t *)drmgr_get_tls_field(drcontext, tls_idx);
    context_handle_t cur_ctxt_hndl = drcctlib_get_context_handle(drcontext, slot);
    // change the order of for loop and if condition
    /*
    for (int i = 0; i < memOp_num; i++){
        if(pt->opList[i].opAddr != 0) {
            AfterWrite(drcontext, cur_ctxt_hndl, &pt->opList[i], num, num_write);
        }
    }
    for (int i = 0; i < num; i++) {
        if (pt->cur_buf_list[i].addr != 0) {
            // store the addr and size of ops in opList[]
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
    */
    BUF_PTR(pt->cur_buf, mem_ref_t, INSTRACE_TLS_OFFS_BUF_PTR) = pt->cur_buf_list;
    
}

// // insert
// static void
// InstrumentMem(void *drcontext, instrlist_t *ilist, instr_t *where, opnd_t ref)
// {
//     /* We need two scratch registers */
//     reg_id_t reg_mem_ref_ptr, free_reg;
//     // for reg_context_handle
//     // reg_id_t reg_ctxt;

//     if (drreg_reserve_register(drcontext, ilist, where, NULL, &reg_mem_ref_ptr) !=
//             DRREG_SUCCESS ||
//         drreg_reserve_register(drcontext, ilist, where, NULL, &free_reg) !=
//             DRREG_SUCCESS) {
//         DRCCTLIB_EXIT_PROCESS("InstrumentMem drreg_reserve_register != DRREG_SUCCESS");
//     }

//     if (!drutil_insert_get_mem_addr(drcontext, ilist, where, ref, free_reg,
//                                     reg_mem_ref_ptr)) {
//         MINSERT(ilist, where,
//                 XINST_CREATE_load_int(drcontext, opnd_create_reg(free_reg),
//                                       OPND_CREATE_CCT_INT(0)));
//     }
//     dr_insert_read_raw_tls(drcontext, ilist, where, tls_seg,
//                            tls_offs + INSTRACE_TLS_OFFS_BUF_PTR, reg_mem_ref_ptr);
//     // store mem_ref_t->addr
//     MINSERT(ilist, where,
//             XINST_CREATE_store(
//                 drcontext, OPND_CREATE_MEMPTR(reg_mem_ref_ptr, offsetof(mem_ref_t, addr)),
//                 opnd_create_reg(free_reg)));

// /*
// #ifdef ARM_CCTLIB
//     MINSERT(ilist, where,
//             XINST_CREATE_load_int(drcontext, opnd_create_reg(free_reg),
//                                   OPND_CREATE_CCT_INT(drutil_opnd_mem_size_in_bytes(ref, where))));
//     MINSERT(ilist, where,
//             XINST_CREATE_store(drcontext, OPND_CREATE_MEMPTR(reg_mem_ref_ptr, offsetof(mem_ref_t, size)),
//                              opnd_create_reg(free_reg)));
// #else
//     MINSERT(ilist, where,
//             XINST_CREATE_store(drcontext, OPND_CREATE_MEMPTR(reg_mem_ref_ptr, offsetof(mem_ref_t, size)),
//                              OPND_CREATE_CCT_INT(drutil_opnd_mem_size_in_bytes(ref, where))));
// #endif
// */

//     // store mem_ref_t->size
//     MINSERT(ilist, where,
//             XINST_CREATE_load_int(drcontext, opnd_create_reg(free_reg),
//                                   OPND_CREATE_CCT_INT(drutil_opnd_mem_size_in_bytes(ref, where))));
//     MINSERT(ilist, where,
//             XINST_CREATE_store(drcontext, OPND_CREATE_MEMPTR(reg_mem_ref_ptr, offsetof(mem_ref_t, size)),
//                              opnd_create_reg(free_reg)));
// // next 
// #ifdef ARM_CCTLIB
//     MINSERT(ilist, where,
//             XINST_CREATE_load_int(drcontext, opnd_create_reg(free_reg),
//                                   OPND_CREATE_CCT_INT(sizeof(mem_ref_t))));
//     MINSERT(ilist, where,
//             XINST_CREATE_add(drcontext, opnd_create_reg(reg_mem_ref_ptr),
//                              opnd_create_reg(free_reg)));
// #else
//     MINSERT(ilist, where,
//             XINST_CREATE_add(drcontext, opnd_create_reg(reg_mem_ref_ptr),
//                              OPND_CREATE_CCT_INT(sizeof(mem_ref_t))));
// #endif

//     dr_insert_write_raw_tls(drcontext, ilist, where, tls_seg,
//                             tls_offs + INSTRACE_TLS_OFFS_BUF_PTR, reg_mem_ref_ptr);
//     /* Restore scratch registers */
//     if (drreg_unreserve_register(drcontext, ilist, where, reg_mem_ref_ptr) !=
//             DRREG_SUCCESS ||
//         drreg_unreserve_register(drcontext, ilist, where, free_reg) != DRREG_SUCCESS) {
//         DRCCTLIB_EXIT_PROCESS("InstrumentMem drreg_unreserve_register != DRREG_SUCCESS");
//     }
// }

static void
InstrumentMemBeforeFirstIns(void *drcontext, instrlist_t *ilist, instr_t *where)
{
    reg_id_t reg_1, reg_2;
    reg_id_t reg_mem_ref_ptr;
    instr_t *skip_to_ptr_next = INSTR_CREATE_label(drcontext); 

#ifdef x86_CCTLIB
    if (drreg_reserve_aflags(drcontext, ilist, where) != DRREG_SUCCESS) {
        DRCCTLIB_EXIT_PROCESS("instrument_before_every_instr_meta_instr "
                            "drreg_reserve_aflags != DRREG_SUCCESS");
    }
#endif
    if (drreg_reserve_register(drcontext, ilist, where, NULL, &reg_mem_ref_ptr) != 
            DRREG_SUCCESS ||
        drreg_reserve_register(drcontext, ilist, where, NULL, &reg_1) != 
            DRREG_SUCCESS ||
        drreg_reserve_register(drcontext, ilist, where, NULL, &reg_2) != 
            DRREG_SUCCESS) {
        DRCCTLIB_EXIT_PROCESS("InstrumentMemBeforeFirstIns drreg_reserve_register != DRREG_SUCCESS");
    }

    dr_insert_read_raw_tls(drcontext, ilist, where, tls_seg,
                           tls_offs + INSTRACE_TLS_OFFS_BUF_PTR, reg_mem_ref_ptr);
    
    MINSERT(ilist, where,
            XINST_CREATE_move(drcontext, opnd_create_reg(reg_1), 
                                OPND_CREATE_MEMPTR(reg_mem_ref_ptr, offsetof(mem_ref_t, addr))));
    MINSERT(ilist, where,
            XINST_CREATE_cmp(drcontext, opnd_create_reg(reg_1), OPND_CREATE_INT32(0)));
    MINSERT(ilist, where,
            XINST_CREATE_jump_cond(drcontext, DR_PRED_Z, opnd_create_instr(skip_to_ptr_next)));
    
    MINSERT(ilist, where,
            XINST_CREATE_move(drcontext, opnd_create_reg(reg_2), OPND_CREATE_MEMPTR(reg_1, 0)));
    
    MINSERT(ilist, where, XINST_CREATE_store(drcontext, 
                                             OPND_CREATE_MEMPTR(reg_mem_ref_ptr, offsetof(mem_ref_t, value)), 
                                             opnd_create_reg(reg_2)));
    // test
    MINSERT(ilist, where,
            XINST_CREATE_move(drcontext, opnd_create_reg(reg_1), 
                                OPND_CREATE_MEMPTR(reg_mem_ref_ptr, offsetof(mem_ref_t, size))));
    // MINSERT(ilist, where,
    //         XINST_CREATE_cmp(drcontext, opnd_create_reg(reg_1), OPND_CREATE_INT32(0)));
    // MINSERT(ilist, where,
    //         XINST_CREATE_jump_cond(drcontext, DR_PRED_Z, opnd_create_instr(skip_to_ptr_next)));
    
    // MINSERT(ilist, where,
    //         XINST_CREATE_move(drcontext, opnd_create_reg(reg_2), OPND_CREATE_MEMPTR(reg_1, 0)));
    
    MINSERT(ilist, where, XINST_CREATE_store(drcontext, 
                                             OPND_CREATE_MEMPTR(reg_mem_ref_ptr, offsetof(mem_ref_t, value_size)), 
                                             opnd_create_reg(reg_1)));
    
    dr_fprintf(gTraceFile, "BeforeFirstIns\n");

    MINSERT(ilist, where, skip_to_ptr_next);


    // Restore scratch registers
    if (drreg_unreserve_register(drcontext, ilist, where, reg_mem_ref_ptr) !=
            DRREG_SUCCESS ||
        drreg_unreserve_register(drcontext, ilist, where, reg_1) != 
            DRREG_SUCCESS ||
        drreg_unreserve_register(drcontext, ilist, where, reg_2) != 
            DRREG_SUCCESS) {
        DRCCTLIB_EXIT_PROCESS("InstrumentMemBeforeFirstIns drreg_unreserve_register != DRREG_SUCCESS");
    }

#ifdef x86_CCTLIB
    if (drreg_unreserve_aflags(drcontext, ilist, where) != DRREG_SUCCESS) {
        DRCCTLIB_EXIT_PROCESS("drreg_unreserve_aflags != DRREG_SUCCESS");
    }
#endif
}


// insert
static void
InstrumentMem2(void *drcontext, instrlist_t *ilist, instr_t *where, opnd_t ref, reg_id_t reg_ctxt_hndl)
{
    // dr_fprintf(gTraceFile, "In Mem2\n");
    reg_id_t reg_1, reg_2, reg_3;
    reg_id_t reg_mem_ref_ptr;
    instr_t *skip_to_ptr_next = INSTR_CREATE_label(drcontext);
    if (drreg_reserve_register(drcontext, ilist, where, NULL, &reg_mem_ref_ptr) != 
            DRREG_SUCCESS ||
        drreg_reserve_register(drcontext, ilist, where, NULL, &reg_1) != 
            DRREG_SUCCESS ||
        drreg_reserve_register(drcontext, ilist, where, NULL, &reg_2) != 
            DRREG_SUCCESS) {
        DRCCTLIB_EXIT_PROCESS("InstrumentMem2 drreg_reserve_register != DRREG_SUCCESS");
    }

    dr_insert_read_raw_tls(drcontext, ilist, where, tls_seg,
                           tls_offs + INSTRACE_TLS_OFFS_BUF_PTR, reg_mem_ref_ptr);
    
    MINSERT(ilist, where,
            XINST_CREATE_move(drcontext, opnd_create_reg(reg_1), 
                                OPND_CREATE_MEMPTR(reg_mem_ref_ptr, offsetof(mem_ref_t, addr))));

    MINSERT(ilist, where,
            XINST_CREATE_cmp(drcontext, opnd_create_reg(reg_1), OPND_CREATE_INT32(0)));
    MINSERT(ilist, where,
            XINST_CREATE_jump_cond(drcontext, DR_PRED_Z, opnd_create_instr(skip_to_ptr_next)));
    
    MINSERT(ilist, where,
            XINST_CREATE_move(drcontext, opnd_create_reg(reg_2), OPND_CREATE_MEMPTR(reg_1, 0)));
    
    MINSERT(ilist, where, XINST_CREATE_store(drcontext, 
                                             OPND_CREATE_MEMPTR(reg_mem_ref_ptr, offsetof(mem_ref_t, value)), 
                                             opnd_create_reg(reg_2)));
    
    // // get size of stored value
    // MINSERT(ilist, where, XINST_CREATE_load_int(drcontext, 
    //                                             opnd_create_reg(reg_2),
    //                                             OPND_CREATE_CCT_INT(drutil_opnd_mem_size_in_bytes(ref, where))));
    // MINSERT(ilist, where, XINST_CREATE_store(drcontext, 
    //                                          OPND_CREATE_MEMPTR(reg_mem_ref_ptr, offsetof(mem_ref_t, value_size)), 
    //                                          opnd_create_reg(reg_2)));

    MINSERT(ilist, where, skip_to_ptr_next);
    // next
    MINSERT(ilist, where,
            XINST_CREATE_load_int(drcontext, opnd_create_reg(reg_1),
                                  OPND_CREATE_CCT_INT(sizeof(mem_ref_t))));
    MINSERT(ilist, where,
            XINST_CREATE_add(drcontext, opnd_create_reg(reg_mem_ref_ptr),
                             opnd_create_reg(reg_1)));
    
    if (!drutil_insert_get_mem_addr(drcontext, ilist, where, ref, reg_1, reg_2)) {
        MINSERT(ilist, where,
                XINST_CREATE_load_int(drcontext, opnd_create_reg(reg_1), OPND_CREATE_CCT_INT(0)));
    }

    // store mem_ref_t->addr
    MINSERT(ilist, where, XINST_CREATE_store(drcontext, 
                                             OPND_CREATE_MEMPTR(reg_mem_ref_ptr, offsetof(mem_ref_t, addr)), 
                                             opnd_create_reg(reg_1)));
    // store mem_ref_t->ctxt_hndl
    MINSERT(ilist, where, XINST_CREATE_store(drcontext,
                                             OPND_CREATE_MEMPTR(reg_mem_ref_ptr, offsetof(mem_ref_t, ctxt_hndl)), 
                                             opnd_create_reg(reg_ctxt_hndl)));
    // store mem_ref_t->size
    MINSERT(ilist, where, XINST_CREATE_load_int(drcontext, 
                                                opnd_create_reg(reg_1),
                                                OPND_CREATE_CCT_INT(drutil_opnd_mem_size_in_bytes(ref, where))));
    MINSERT(ilist, where, XINST_CREATE_store(drcontext, 
                                             OPND_CREATE_MEMPTR(reg_mem_ref_ptr, offsetof(mem_ref_t, size)), 
                                             opnd_create_reg(reg_1)));

    dr_insert_write_raw_tls(drcontext, ilist, where, tls_seg,
                            tls_offs + INSTRACE_TLS_OFFS_BUF_PTR, reg_mem_ref_ptr);

    // Restore scratch registers
    if (drreg_unreserve_register(drcontext, ilist, where, reg_mem_ref_ptr) !=
            DRREG_SUCCESS ||
        drreg_unreserve_register(drcontext, ilist, where, reg_1) != 
            DRREG_SUCCESS ||
        drreg_unreserve_register(drcontext, ilist, where, reg_2) !=
            DRREG_SUCCESS) {
        DRCCTLIB_EXIT_PROCESS("InstrumentMem2 drreg_unreserve_register != DRREG_SUCCESS");
    }
}


// Instrumentation function the beginning of basic block
void 
InstrumentBBStartInsertCallback(int32_t mem_ref_num) {
    void * drcontext = dr_get_current_drcontext();
    per_thread_t *pt = (per_thread_t *)drmgr_get_tls_field(drcontext, tls_idx);
    //dr_fprintf(gTraceFile, "BBStartInsertCallback\n");
    
    
    dr_fprintf(gTraceFile, "pt->last_bb_mem_ref_num = %d\n", pt->last_bb_mem_ref_num);

    for (uint64_t i = 1; i < pt->last_bb_mem_ref_num + 1; i++) {
        if (pt->cur_buf_list[i].addr != 0) {
            dr_fprintf(gTraceFile, "%llu addr = %p value = %llu\n", i, pt->cur_buf_list[i].addr, pt->cur_buf_list[i].value);
            dr_fprintf(gTraceFile, "!! value size = %lu\n", pt->cur_buf_list[i].value_size);
            dr_fprintf(gTraceFile, "size = %lu\n", pt->cur_buf_list[i].size);
            
            // store the addr and size of ops in opList[]
            // check the values in addr after running ins
            // pt->opList[i].opAddr = (uint64_t*)((&pt->cur_buf_list[i])->addr);
            // pt->opList[i].opSize = (uint32_t)((&pt->cur_buf_list[i])->size);
            // BeforeWrite(drcontext, cur_ctxt_hndl, &pt->cur_buf_list[i], num, num_write);
        } else {
            // pt->opList[i].opAddr = 0;
            // pt->opList[i].opSize = 0;
        }
    }
    pt->last_bb_mem_ref_num = mem_ref_num;
    BUF_PTR(pt->cur_buf, mem_ref_t, INSTRACE_TLS_OFFS_BUF_PTR) = pt->cur_buf_list;
}



// analysis
void
InstrumentInsCallback(void *drcontext, instr_instrument_msg_t *instrument_msg)
{
    if (!instrument_msg->interest_start) {
        return;
    }

    instrlist_t *bb = instrument_msg->bb;
    int bb_num_write = 0;
    for (instr_instrument_msg_t* cur = instrument_msg; cur != NULL; cur = cur->next) {
        instr_t *instr =  cur->instr;
        for (int i = 0; i < instr_num_dsts(instr); i++) {
            if (opnd_is_memory_reference(instr_get_dst(instr, i)) && drutil_opnd_mem_size_in_bytes(instr_get_dst(instr, i), instr) == 8) { //dst = write
                bb_num_write++;
            }
        }
    }
    if (bb_num_write <= 0) {
        return;
    }
    dr_fprintf(gTraceFile, "bb_num_write = %d\n", bb_num_write);
    
    InstrumentMemBeforeFirstIns(drcontext, bb, instrument_msg->instr);

    dr_insert_clean_call(drcontext, bb, instrument_msg->instr, (void *)InstrumentBBStartInsertCallback, false, 1,
                         OPND_CREATE_CCT_INT(bb_num_write));

    for (instr_instrument_msg_t* cur = instrument_msg; cur != NULL; cur = cur->next) {
        int32_t slot = cur->slot;
        instr_t *instr = cur->instr;

#ifdef x86_CCTLIB
        if (drreg_reserve_aflags(drcontext, bb, instr) != DRREG_SUCCESS) {
            DRCCTLIB_EXIT_PROCESS("instrument_before_every_instr_meta_instr "
                                "drreg_reserve_aflags != DRREG_SUCCESS");
        }
#endif
        reg_id_t reg_ctxt_hndl, free_reg;
        if (drreg_reserve_register(drcontext, bb, instr, NULL, &reg_ctxt_hndl) != 
                DRREG_SUCCESS || 
            drreg_reserve_register(drcontext, bb, instr, NULL, &free_reg) != 
                DRREG_SUCCESS) {
            DRCCTLIB_EXIT_PROCESS(
                "InstrumentInsCallback drreg_reserve_register != DRREG_SUCCESS");    
        }
        drcctlib_get_context_handle_in_reg(drcontext, bb, instr, slot, reg_ctxt_hndl, 
                                        free_reg);
        for (int i = 0; i < instr_num_dsts(instr); i++) {
            // TODO
            if (opnd_is_memory_reference(instr_get_dst(instr, i)) && drutil_opnd_mem_size_in_bytes(instr_get_dst(instr, i), instr) == 8) { //dst = write
                InstrumentMem2(drcontext, bb, instr, instr_get_dst(instr, i), reg_ctxt_hndl);
            }
        }
        if (drreg_unreserve_register(drcontext, bb, instr, reg_ctxt_hndl) !=
                DRREG_SUCCESS ||
            drreg_unreserve_register(drcontext, bb, instr, free_reg) != 
                DRREG_SUCCESS) {
            DRCCTLIB_EXIT_PROCESS("InstrumentMem2 drreg_unreserve_register != DRREG_SUCCESS");
        }
#ifdef x86_CCTLIB
        if (drreg_unreserve_aflags(drcontext, bb, instr) != DRREG_SUCCESS) {
            DRCCTLIB_EXIT_PROCESS("drreg_unreserve_aflags != DRREG_SUCCESS");
        }
#endif
    }
}





static bool 
RedundancyCompare(const struct RedanduncyData &first, const struct RedanduncyData &second) {
    return first.frequency > second.frequency ? true : false;
}

void 
PrintRedundancyPairs(void * drcontext,int threadID) {
    vector<RedanduncyData> tmpList;
    vector<RedanduncyData>::iterator tmpIt;
    uint64_t grandTotalRedundantBytes = 0;
    //dr_fprintf(gTraceFile, "********** Dump Data from Thread %d **********\n", threadID);
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

    // GUI
    // dr_mutex_lock(lock);
    Profile::profile_t *profile = new Profile::profile_t();
    profile->add_metric_type(1, "times", "instruction execute times");
    // should be executed before map clear
    
    for (int i = 0; i < TOP_REACH_NUM_SHOW; i ++) {
        if ((*listIt).dead == 0) {
            break;
        }
        // metric needs to be adjusted
        /*
        inner_context_t *cur_ctxt = drcctlib_get_full_cct((*listIt).dead);
        profile->add_sample(cur_ctxt)->append_metirc((*listIt).frequency);
        drcctlib_free_full_cct(cur_ctxt);
        */
    }
    
    // profile->serialize_to_file("test.drcctprof");
    // dr_mutex_unlock(lock);
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
    pt->last_bb_mem_ref_num = 0;
    pt->last_mem_idx = 0;
    pt->cur_mem_idx = 0;
    pt->cur_buf_fill_num = 0;
    BUF_PTR(pt->cur_buf, mem_ref_t, INSTRACE_TLS_OFFS_BUF_PTR) = pt->cur_buf_list;

}

static void
ClientThreadEnd(void *drcontext)
{
    dr_fprintf(gTraceFile, "ThreadEnd\n");
    per_thread_t *pt = (per_thread_t *)drmgr_get_tls_field(drcontext, tls_idx);
    //InstrumentBBStartInsertCallback(drcontext, 0, TLS_MEM_REF_BUFF_SIZE);
    
    int threadID = drcctlib_get_thread_id();
    // need lock for drcctlib_have_same_source_line
    dr_mutex_lock(lock);
    PrintRedundancyPairs(drcontext, threadID);
    dr_mutex_unlock(lock);
    /*
    // GUI
    Profile::profile_t *profile = new Profile::profile_t();
    //profile->add_metric_type(1, "times", "instruction execute times");
    // should be executed before map clear
    
    for (int i = 0; i < TOP_REACH_NUM_SHOW; i ++) {
        if (output_list[i].handle == 0) {
            break;
        }
        inner_context_t *cur_ctxt = drcctlib_get_full_cct(output_list[i].handle);
        profile->add_sample(cur_ctxt)->append_metirc(output_list[i].count);
        drcctlib_free_full_cct(cur_ctxt);
    }
    profile->serialize_to_file("redspy.drcctprof");
    delete profile;
    */
    
    // clear the map
    RedMap[threadID].clear();

    dr_global_free(pt->cur_buf_list, TLS_MEM_REF_BUFF_SIZE * sizeof(mem_ref_t));
    // delete pt->tls_use_map;
    dr_thread_free(drcontext, pt, sizeof(per_thread_t));
}

static void  
ClientInit(int argc, const char *argv[])
{
    char name[MAXIMUM_PATH] = "";
    DRCCTLIB_INIT_LOG_FILE_NAME(name, "testred", "out");
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
            "ERROR: drcctlib_test dr_raw_tls_calloc fail");
    }
    if (!drmgr_unregister_thread_init_event(ClientThreadStart) ||
        !drmgr_unregister_thread_exit_event(ClientThreadEnd) ||
        !drmgr_unregister_tls_field(tls_idx)) {
        DRCCTLIB_PRINTF("ERROR: drcctlib_test failed to "
                        "unregister in ClientExit");
    }
    drmgr_exit();
    if (drreg_exit() != DRREG_SUCCESS) {
        DRCCTLIB_PRINTF("failed to exit drreg");
    }
    drutil_exit();
    dr_mutex_destroy(lock);
}


#ifdef __cplusplus
extern "C" {
#endif



DR_EXPORT void
dr_client_main(client_id_t id, int argc, const char *argv[])
{
    dr_set_client_name("DynamoRIO Client 'drcctlib_test'",
                       "http://dynamorio.org/issues");
    ClientInit(argc, argv);

    if (!drmgr_init()) {
        DRCCTLIB_EXIT_PROCESS("ERROR: drcctlib_test "
                              "unable to initialize drmgr");
    }
    drreg_options_t ops = { sizeof(ops), 4 /*max slots needed*/, false };
    if (drreg_init(&ops) != DRREG_SUCCESS) {
        DRCCTLIB_EXIT_PROCESS("ERROR: drcctlib_test "
                              "unable to initialize drreg");
    }
    if (!drutil_init()) {
        DRCCTLIB_EXIT_PROCESS("ERROR: drcctlib_test "
                              "unable to initialize drutil");
    }
    drmgr_register_thread_init_event(ClientThreadStart);
    drmgr_register_thread_exit_event(ClientThreadEnd);

    tls_idx = drmgr_register_tls_field();
    if (tls_idx == -1) {
        DRCCTLIB_EXIT_PROCESS("ERROR: drcctlib_test "
                              "drmgr_register_tls_field fail");
    }
    if (!dr_raw_tls_calloc(&tls_seg, &tls_offs, INSTRACE_TLS_COUNT, 0)) {
        DRCCTLIB_EXIT_PROCESS(
            "ERROR: drcctlib_test dr_raw_tls_calloc fail");
    }
    // drcctlib_init(CustomFilter, INVALID_FILE, InstrumentInsCallback, false);
    // drcctlib_init(DRCCTLIB_FILTER_MEM_ACCESS_INSTR, INVALID_FILE, InstrumentInsCallback, false);
    drcctlib_init_ex(CustomFilter, INVALID_FILE, InstrumentInsCallback, NULL, NULL, 
                    DRCCTLIB_COLLECT_DATA_CENTRIC_MESSAGE);
    // add print function
    dr_register_exit_event(ClientExit);
}

#ifdef __cplusplus
}
#endif
