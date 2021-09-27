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

using namespace std;

#define DRCCTLIB_PRINTF(_FORMAT, _ARGS...) \
    DRCCTLIB_PRINTF_TEMPLATE("memory_with_addr_and_refsize_clean_call", _FORMAT, ##_ARGS)
#define DRCCTLIB_EXIT_PROCESS(_FORMAT, _ARGS...)                                           \
    DRCCTLIB_CLIENT_EXIT_PROCESS_TEMPLATE("memory_with_addr_and_refsize_clean_call", _FORMAT, \
                                          ##_ARGS)

static int tls_idx;

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
    app_pc addr;
    size_t size;
} mem_ref_t;

typedef struct _per_thread_t {
    mem_ref_t *cur_buf_list;
    void *cur_buf;
} per_thread_t;

//void *lock;

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

/*
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
*/


void
DoWhatClientWantToDo(void *drcontext, context_handle_t cur_ctxt_hndl, mem_ref_t *ref){
    
}

// dr clean call
void
InsertCleancall(int32_t slot, int32_t num, int32_t num_write)
{
    void *drcontext = dr_get_current_drcontext();
    per_thread_t *pt = (per_thread_t *)drmgr_get_tls_field(drcontext, tls_idx);
    context_handle_t cur_ctxt_hndl = drcctlib_get_context_handle(drcontext, slot);
    
    /*
    // change the order of for loop and if condition
    for (int i = 0; i < memOp_num; i++){
        if(pt->opList[i].opAddr != 0) {
            AfterWrite(drcontext, cur_ctxt_hndl, &pt->opList[i], num, num_write);
        }
    }
    */
    for (int i = 0; i < num; i++) {
        if (pt->cur_buf_list[i].addr != 0) {
            DoWhatClientWantToDo(drcontext, cur_ctxt_hndl, &pt->cur_buf_list[i]);
        }
    }
    //memOp_num = num;
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
    //int num_read = 0;
    int num_write = 0;
    //int op = 0; //read is 0, write is 1

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
}

static void
ClientInit(int argc, const char *argv[])
{
    char name[MAXIMUM_PATH] = "";
    DRCCTLIB_INIT_LOG_FILE_NAME(name, "test", "out");
    gTraceFile = dr_open_file(name, DR_FILE_WRITE_OVERWRITE | DR_FILE_ALLOW_LARGE);
    DR_ASSERT(gTraceFile != INVALID_FILE);
    dr_fprintf(gTraceFile, "ClientInit\n");
    //lock = dr_mutex_create();
    
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
    //dr_mutex_destroy(lock);
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
