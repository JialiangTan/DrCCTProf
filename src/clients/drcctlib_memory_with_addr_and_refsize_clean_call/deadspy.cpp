/* 
 *  Copyright (c) 2020-2021 Xuhpclab. All rights reserved.
 *  Licensed under the MIT License.
 *  See LICENSE file for more information.
 */

#include <cstddef>
#include <unordered_map>
#include <map>
#include<sys/mman.h>
#include <list>
#include <stdint.h>
#include <unistd.h>
#include <iostream>

#include "dr_api.h"
#include "drmgr.h"
#include "drreg.h"
#include "drutil.h"
#include "drcctlib.h"
//#include "shadow_memory.h"
//#include "shadow_memory_ml.h"


using namespace std;

#define OUTPUT_SIZE 20
#define DRCCTLIB_PRINTF(_FORMAT, _ARGS...) \
    DRCCTLIB_PRINTF_TEMPLATE("memory_with_addr_and_refsize_clean_call", _FORMAT, ##_ARGS)
#define DRCCTLIB_EXIT_PROCESS(_FORMAT, _ARGS...)                                           \
    DRCCTLIB_CLIENT_EXIT_PROCESS_TEMPLATE("memory_with_addr_and_refsize_clean_call", _FORMAT, \
                                          ##_ARGS)

#define MAX_CLIENT_CCT_PRINT_DEPTH 3
#define MAX_DEAD_CONTEXTS_TO_LOG 100

static int tls_idx;
static file_t gTraceFile;
volatile uint32_t NumThreads;

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

typedef struct DeadInfo {
    void* firstIP;
    void* secondIP;
    uint64_t count;
} DeadInfo;

typedef struct MergedDeadInfo {
    uint32_t context1;
    uint32_t context2;

    bool operator == (const MergedDeadInfo& x) const {
        if (this->context1 == x.context1 && this->context2 == x.context2)
	    return true;
	return false;
    }

    bool operator < (const MergedDeadInfo& x) const {
        if ((this->context1 < x.context1) || (this->context1 == x.context1 && this->context2 < x.context2))
	    return true;
	return false;
    }
} MergedDeadInfo;

typedef struct DeadInfoForPresentation {
    const MergedDeadInfo *pMergedDeadInfo;
    uint64_t count;
} DeadInfoForPresentation;

//ConcurrentShadowMemory<uint8_t> shadow_mem;
//ConcurrentShadowMemoryMl<uint8_t> shadow_mem;


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

#define LEVEL_1_PAGE_TABLE_SLOT(addr) ((((uint64_t)addr) >> (LEVEL_2_PAGE_TABLE_BITS + PAGE_OFFSET_BITS)) & 0xfffff)
#define LEVEL_2_PAGE_TABLE_SLOT(addr) ((((uint64_t)addr) >> (PAGE_OFFSET_BITS)) & 0xFFF)




// ensures CONTINUOUS_DEADINFO
#define CONTINUOUS_DEADINFO

#if defined(CONTINUOUS_DEADINFO)
unordered_map<uint64_t, uint64_t> DeadMap;
unordered_map<uint64_t, uint64_t>::iterator gDeadMapIt;
#else // no defined(CONTINUOUS_DEADINFO)
unordered_map<uint64_t, DeadInfo> DeadMap;
unordered_map<uint64_t, DeadInfo>::iterator gDeadMapIt;
#endif //end defined(CONTINUOUS_DEADINFO) 


#define TLS_MEM_REF_BUFF_SIZE 100

#define ONE_BYTE_READ_ACTION (0)
#define TWO_BYTE_READ_ACTION (0)
#define FOUR_BYTE_READ_ACTION (0)
#define EIGHT_BYTE_READ_ACTION (0)

#define ONE_BYTE_WRITE_ACTION (0xff)
#define TWO_BYTE_WRITE_ACTION (0xffff)
#define FOUR_BYTE_WRITE_ACTION (0xffffffff)
#define EIGHT_BYTE_WRITE_ACTION (0xffffffffffffffff)



// make 64bit hash from 2 32bit deltas from
// remove lower 3 bits so that when we need more than 4 GB HASH still continues to work

#if 0
#define CONTEXT_HASH_128BITS_TO_64BITS(curCtxt, oldCtxt, hashVar)  \
{\
uint64_t key = (uint64_t) (((void**)oldCtxt) - gPreAllocatedContextBuffer); \
hashVar = key << 32;\
key = (uint64_t) (((void**)curCtxt) - gPreAllocatedContextBuffer); \
hashVar |= key;\
}
#else
#define CONTEXT_HASH_128BITS_TO_64BITS(curCtxt, oldCtxt, hashVar)  \
{\
uint64_t key = (uint64_t) (oldCtxt); \
hashVar = key << 32;\
key = (uint64_t) (curCtxt); \
hashVar |= key;\
}
#endif



#if defined(CONTINUOUS_DEADINFO)
#define DECLARE_HASHVAR(name) uint64_t name

#define REPORT_DEAD(curCtxt, lastCtxt, hashVar, size) do { \
CONTEXT_HASH_128BITS_TO_64BITS(curCtxt, lastCtxt, hashVar)  \
if ((gDeadMapIt = DeadMap.find(hashVar))  == DeadMap.end()) {    \
DeadMap.insert(std::pair<uint64_t, uint64_t>(hashVar, size)); \
} else {    \
(gDeadMapIt->second) += size;    \
}   \
}while(0)

#else // no defined(CONTINUOUS_DEADINFO)
#define DECLARE_HASHVAR(name) uint64_t name

#define REPORT_DEAD(curCtxt, lastCtxt, hashVar, size) do { \
CONTEXT_HASH_128BITS_TO_64BITS(curCtxt, lastCtxt, hashVar)  \
if ( (gDeadMapIt = DeadMap.find(hashVar))  == DeadMap.end()) {    \
DeadInfo deadInfo = { lastCtxt,  curCtxt, size };   \
DeadMap.insert(std::pair<uint64_t, DeadInfo>(hashVar, deadInfo)); \
} else {    \
(gDeadMapIt->second.count) += size;    \
}   \
}while(0)

#endif // end defined(CONTINUOUS_DEADINFO)


#define REPORT_IF_DEAD(mask, curCtxt, lastCtxt, hashVar) do {if (state & (mask)){ \
REPORT_DEAD(curCtxt, lastCtxt, hashVar, 1);\
}}while(0)


uint8_t** gL1PageTable[LEVEL_1_PAGE_TABLE_SIZE];
uint64_t gTotalDead = 0;
uint32_t gClientNumThreads = 1;


uint8_t *GetOrCreateShadowBaseAddress(void *addr) {
    uint8_t *shadowPage;
    uint8_t** *l1Ptr = &gL1PageTable[LEVEL_1_PAGE_TABLE_SLOT(addr)];
    
    if (*l1Ptr == 0) {
        *l1Ptr = (uint8_t**) calloc(1, LEVEL_2_PAGE_TABLE_SIZE);
        shadowPage = (*l1Ptr)[LEVEL_2_PAGE_TABLE_SLOT(addr)] = (uint8_t*) mmap(0, PAGE_SIZE * (1 + sizeof(uint32_t)), PROT_WRITE | PROT_READ, MAP_NORESERVE | MAP_PRIVATE | MAP_ANONYMOUS, 0, 0);

    } else if ((shadowPage = (*l1Ptr)[LEVEL_2_PAGE_TABLE_SLOT(addr)]) == 0) {
        shadowPage = (*l1Ptr)[LEVEL_2_PAGE_TABLE_SLOT(addr)] = (uint8_t*) mmap(0, PAGE_SIZE * (1 + sizeof(uint32_t)), PROT_WRITE | PROT_READ, MAP_NORESERVE | MAP_PRIVATE | MAP_ANONYMOUS, 0, 0);
    }
    return shadowPage;
}

inline uint8_t* GetShadowBaseAddress(void *addr){
    uint8_t* shadowPage;
    uint8_t** *l1Ptr = &gL1PageTable[LEVEL_1_PAGE_TABLE_SLOT(addr)];

    if(*l1Ptr == 0){
        return 0;
    } else if ((shadowPage = (*l1Ptr)[LEVEL_2_PAGE_TABLE_SLOT(addr)]) == 0) {
        return 0;
    }

    return shadowPage;
}

void
Record1ByteMemRead(void *addr) {
    uint8_t *status = GetShadowBaseAddress(addr);
    //dr_fprintf(gTraceFile, "addr: %p\n", addr);
    //dr_fprintf(gTraceFile, "GetShadowBaseAddress: 1Byte read status: %p\n", status);
    // status == 0 if not created
    if (status){
        // NOT NEEDED status->lastIP = ip;
        *(status + PAGE_OFFSET((uint64_t)addr))  = ONE_BYTE_READ_ACTION;
        //uint8_t *tmp = status + PAGE_OFFSET((uint64_t)addr);
        //dr_fprintf(gTraceFile, "if (status): %p\n", status);
        //dr_fprintf(gTraceFile, "+offset: %p\n", tmp);
    }
    //dr_fprintf(gTraceFile, "============================\n");
}


void
Record1ByteMemWrite(void *addr, context_handle_t cur_ctxt_hndl){
    //context_handle_t: int32_t
    uint8_t *status = GetOrCreateShadowBaseAddress(addr);
    uint32_t *lastIP = (uint32_t *)(status + PAGE_SIZE + PAGE_OFFSET((uint64_t)addr) * sizeof(uint32_t));    
    //dr_fprintf(gTraceFile, "GetOrCreateShadowBaseAddress: 1Byte write status: %p\n", status);

    if (*(status + PAGE_OFFSET((uint64_t)addr)) == ONE_BYTE_WRITE_ACTION) {
        DECLARE_HASHVAR(myhash);
        REPORT_DEAD(cur_ctxt_hndl, *(lastIP), myhash, 1);
    }
    else {
        *(status + PAGE_OFFSET((uint64_t)addr)) = ONE_BYTE_WRITE_ACTION;
    }
    
    // jtan: crash following line:
    *lastIP = cur_ctxt_hndl;
}


void
Record2ByteMemRead(void *addr){
    uint8_t *status = GetShadowBaseAddress(addr);
    // status == 0 if not created.
    if (PAGE_OFFSET((uint64_t)addr) != PAGE_OFFSET_MASK) {
        if (status) {
            *((uint16_t*)status + PAGE_OFFSET((uint64_t)addr)) = TWO_BYTE_READ_ACTION;
        }
    }
    else {
        if (status) {
            *(status + PAGE_OFFSET_MASK) = ONE_BYTE_READ_ACTION;
        }
        status = GetShadowBaseAddress(((char*)addr) + 1);
        
        if (status) {
            *status = ONE_BYTE_READ_ACTION;
        }
    }
    //dr_fprintf(gTraceFile, "============================\n");
}


void
Record2ByteMemWrite(void *addr, context_handle_t cur_ctxt_hndl) {
    uint8_t *status = GetOrCreateShadowBaseAddress(addr);
    // status == 0 if not created
    if (PAGE_OFFSET((uint64_t)addr) != PAGE_OFFSET_MASK) {
        uint32_t *lastIP = (uint32_t*)(status + PAGE_SIZE + PAGE_OFFSET((uint64_t)addr * sizeof(uint32_t)));
        uint16_t state = *((uint16_t*)(status + PAGE_OFFSET((uint64_t)addr)));
        
        if (state != TWO_BYTE_READ_ACTION) {
            
            DECLARE_HASHVAR(myhash);
            // fast path where all bytes are dead by same context
            if (state == TWO_BYTE_WRITE_ACTION && lastIP[0] == lastIP[1]) {
                REPORT_DEAD(cur_ctxt_hndl, *(lastIP), myhash, 2);
                // State is already written, so no need to dead write in a tool that detects dead writes
            } else {
                // slow path
                // byte 1 dead ?
		        REPORT_IF_DEAD(0x00ff, cur_ctxt_hndl, lastIP[0], myhash);
		        // byte 2 dead ?
		        REPORT_IF_DEAD(0xff00, cur_ctxt_hndl, lastIP[1], myhash);
		        // update state for all
		        *((uint16_t*)(status + PAGE_OFFSET((uint64_t)addr))) = TWO_BYTE_WRITE_ACTION;
	        }
	    } else {
	        // record as written
	        *((uint16_t*)(status + PAGE_OFFSET((uint64_t)addr))) = TWO_BYTE_WRITE_ACTION;
	    }

	    lastIP[0] = cur_ctxt_hndl;
	    lastIP[1] = cur_ctxt_hndl;
    }
    else {
        Record1ByteMemWrite(addr, cur_ctxt_hndl);
        Record1ByteMemWrite(((char*)addr) + 1, cur_ctxt_hndl);
    }
}


void
Record4ByteMemRead(void *addr) {
    uint8_t *status = GetShadowBaseAddress(addr);
    //dr_fprintf(gTraceFile, "4Byte read status: %p\n", status);
    int overflow = PAGE_OFFSET((uint64_t)addr) - (PAGE_OFFSET_MASK - 3);

    if (overflow <= 0) {
        if (status) {
            *((uint32_t*)(status + PAGE_OFFSET((uint64_t)addr)))  = FOUR_BYTE_READ_ACTION;
        }
    } else {
        if (status) {
            status += PAGE_OFFSET((uint64_t)addr);
            
            for (int nonOverflowBytes = 0; nonOverflowBytes < 4 - overflow; nonOverflowBytes++) {
                *(status++) = ONE_BYTE_READ_ACTION;
	        }
	    }

	    status = GetShadowBaseAddress(((char*)addr) + 4); // +4 so that we get next page

	    if (status) {
	        for (; overflow; overflow--) {
	            *(status++) = ONE_BYTE_READ_ACTION;
	        }
	    }
    }
}


void
Record4ByteMemWrite(void *addr, context_handle_t cur_ctxt_hndl) {
    uint8_t *status = GetOrCreateShadowBaseAddress(addr);
    //dr_fprintf(gTraceFile, "4Byte write status: %p\n", status);

    if (PAGE_OFFSET((uint64_t)addr) < (PAGE_OFFSET_MASK - 2)) {
        uint32_t *lastIP = (uint32_t*)(status + PAGE_SIZE + PAGE_OFFSET((uint64_t)addr) * sizeof(uint32_t));
        uint32_t state = *((uint32_t*)(status + PAGE_OFFSET((uint64_t)addr)));
        
        if (state != FOUR_BYTE_READ_ACTION) {
            DECLARE_HASHVAR(myhash);
            uint32_t ipZero = lastIP[0];
            
            // fast path where all bytes are dead by same context
            if (state == FOUR_BYTE_WRITE_ACTION && 
                    ipZero == lastIP[0] && ipZero == lastIP[1] && ipZero == lastIP[2] && ipZero == lastIP[3]) {
                REPORT_DEAD(cur_ctxt_hndl, ipZero, myhash, 4);
		        // State is already written, so no need to dead write in a tool that detects dead writes
	        } else {
	            // slow path
		        // byte 1 dead ?
		        REPORT_IF_DEAD(0x000000ff, cur_ctxt_hndl, ipZero, myhash);
		        // byte 2 dead ?
		        REPORT_IF_DEAD(0x0000ff00, cur_ctxt_hndl, lastIP[1], myhash);
		        // byte 3 dead ?
		        REPORT_IF_DEAD(0x00ff0000, cur_ctxt_hndl, lastIP[2], myhash);
		        // byte 4 dead ?
		        REPORT_IF_DEAD(0xff000000, cur_ctxt_hndl, lastIP[3], myhash);
		        // update state for all 
		        *((uint32_t*)(status + PAGE_OFFSET((uint64_t)addr))) = FOUR_BYTE_WRITE_ACTION;
	        }
	    } else {
	        // record as written
	        *((uint32_t*)(status + PAGE_OFFSET((uint64_t)addr))) = FOUR_BYTE_WRITE_ACTION;
	    }
	    lastIP[0] = cur_ctxt_hndl;
	    lastIP[1] = cur_ctxt_hndl;
	    lastIP[2] = cur_ctxt_hndl;
	    lastIP[3] = cur_ctxt_hndl;
    } else {
        Record1ByteMemWrite(addr, cur_ctxt_hndl);
        Record1ByteMemWrite(((char*)addr) + 1, cur_ctxt_hndl);
        Record1ByteMemWrite(((char*)addr) + 2, cur_ctxt_hndl);
        Record1ByteMemWrite(((char*)addr) + 3, cur_ctxt_hndl);
    }
}


void
Record8ByteMemRead(void *addr) {
    uint8_t *status = GetShadowBaseAddress(addr);
    // status == 0 if not created
    //dr_fprintf(gTraceFile, "8Byte read status %p\n", status);
    int overflow = PAGE_OFFSET((uint64_t)addr) - (PAGE_OFFSET_MASK - 7);

    if (overflow <= 0) {
        if (status) {
            *((uint64_t*)(status + PAGE_OFFSET((uint64_t)addr))) = EIGHT_BYTE_READ_ACTION;
        }
    } else {
        if (status) {
	        status += PAGE_OFFSET((uint64_t)addr);

	        for (int nonOverflowBytes = 0; nonOverflowBytes < 8 - overflow; nonOverflowBytes++) {
	            *(status++) = ONE_BYTE_READ_ACTION;
	        }
	    }

	    status = GetShadowBaseAddress(((char*)addr) + 8);  // +8 so that we get next page

	    if (status) {
	        for (; overflow; overflow--) {
	            *(status++) = ONE_BYTE_READ_ACTION;
	        }
	    }
    }
}


void
Record8ByteMemWrite(void *addr, context_handle_t cur_ctxt_hndl) {
    // jtan: crash following line:
    uint8_t *status = GetOrCreateShadowBaseAddress(addr);
    //dr_fprintf(gTraceFile, "8Byte write status %p\n", status);
    // status == 0 if not created
    
    if (PAGE_OFFSET((uint64_t)addr) < (PAGE_OFFSET_MASK - 6)) {
        uint32_t* lastIP = (uint32_t*)(status + PAGE_SIZE + PAGE_OFFSET((uint64_t)addr) * sizeof(uint32_t));
	    uint64_t state = *((uint64_t*)(status + PAGE_OFFSET((uint64_t)addr)));
    
        if (state != EIGHT_BYTE_WRITE_ACTION) {
            DECLARE_HASHVAR(myhash);
            uint32_t ipZero = lastIP[0];
        
            // fast path where all bytes are dead by same context
            if (state == EIGHT_BYTE_WRITE_ACTION &&
                    ipZero == lastIP[1] && ipZero == lastIP[2] && 
                    ipZero == lastIP[3] && ipZero == lastIP[4] &&
                    ipZero == lastIP[5] && ipZero == lastIP[6] &&
                    ipZero == lastIP[7]) {
                REPORT_DEAD(cur_ctxt_hndl, ipZero, myhash, 8);
                // State is already written, so no need to dead write in a tool that detects dead writes
            } else {
                // slow path
                // byte 1 dead?
                REPORT_IF_DEAD(0x00000000000000ff, cur_ctxt_hndl, ipZero, myhash);
                // byte 2 dead?
                REPORT_IF_DEAD(0x000000000000ff00, cur_ctxt_hndl, lastIP[1], myhash);
                // byte 3 dead?
                REPORT_IF_DEAD(0x0000000000ff0000, cur_ctxt_hndl, lastIP[2], myhash);
                // byte 4 dead?
                REPORT_IF_DEAD(0x00000000ff000000, cur_ctxt_hndl, lastIP[3], myhash);
                // byte 5 dead?
                REPORT_IF_DEAD(0x000000ff00000000, cur_ctxt_hndl, lastIP[4], myhash);
                // byte 6 dead?
                REPORT_IF_DEAD(0x0000ff0000000000, cur_ctxt_hndl, lastIP[5], myhash);
                // byte 7 dead?
                REPORT_IF_DEAD(0x00ff000000000000, cur_ctxt_hndl, lastIP[6], myhash);
                // byte 7 dead?
                REPORT_IF_DEAD(0xff00000000000000, cur_ctxt_hndl, lastIP[7], myhash);
                // update state for all
                *((uint64_t*)(status + PAGE_OFFSET((uint64_t)addr))) = EIGHT_BYTE_WRITE_ACTION;
            }
        } else {
            // record as written
            *((uint64_t*)(status + PAGE_OFFSET((uint64_t)addr))) = EIGHT_BYTE_WRITE_ACTION;
        }
        lastIP[0] = cur_ctxt_hndl;
        lastIP[1] = cur_ctxt_hndl;
        lastIP[2] = cur_ctxt_hndl;
        lastIP[3] = cur_ctxt_hndl;
        lastIP[4] = cur_ctxt_hndl;
        lastIP[5] = cur_ctxt_hndl;
        lastIP[6] = cur_ctxt_hndl;
        lastIP[7] = cur_ctxt_hndl;
    } else {
        Record1ByteMemWrite(addr, cur_ctxt_hndl);
        Record1ByteMemWrite(((char*)addr) + 1, cur_ctxt_hndl);
        Record1ByteMemWrite(((char*)addr) + 2, cur_ctxt_hndl);
        Record1ByteMemWrite(((char*)addr) + 3, cur_ctxt_hndl);
        Record1ByteMemWrite(((char*)addr) + 4, cur_ctxt_hndl);
        Record1ByteMemWrite(((char*)addr) + 5, cur_ctxt_hndl);
        Record1ByteMemWrite(((char*)addr) + 6, cur_ctxt_hndl);
        Record1ByteMemWrite(((char*)addr) + 7, cur_ctxt_hndl);
    }
}



void
Record10ByteMemRead(void *addr) {
    uint8_t *status = GetShadowBaseAddress(addr);
    //dr_fprintf(gTraceFile, "10Byte read status %p\n", status);
    int overflow = PAGE_OFFSET((uint64_t)addr) - (PAGE_OFFSET_MASK - 15);

    if(overflow <= 0) {
        if (status) {
            *((uint64_t*)(status + PAGE_OFFSET((uint64_t)addr))) = EIGHT_BYTE_READ_ACTION;
            *((uint16_t*)(status + PAGE_OFFSET(((uint64_t)addr + 8)))) = TWO_BYTE_READ_ACTION;
        }
    } else {
        // slow path
        Record8ByteMemRead(addr);
        Record2ByteMemRead((char*)addr + 8);
    }
}


void 
Record10ByteMemWrite(void *addr, context_handle_t cur_ctxt_hndl) {
    uint8_t *status = GetOrCreateShadowBaseAddress(addr);
    //dr_fprintf(gTraceFile, "10Byte write status %p\n", status);
    // status == 0 if not created

    if (PAGE_OFFSET((uint64_t)addr) < (PAGE_OFFSET_MASK - 8)) {
        uint32_t *lastIP = (uint32_t*)(status + PAGE_SIZE + PAGE_OFFSET((uint64_t)addr) * sizeof(uint32_t));
        uint64_t state = *((uint64_t*)(status + PAGE_OFFSET((uint64_t)addr)));

        if (state != EIGHT_BYTE_READ_ACTION) {
            DECLARE_HASHVAR(myhash);
            uint32_t ipZero = lastIP[0];

            // fast path where all bytes all dead by the same context
            if (state == EIGHT_BYTE_WRITE_ACTION &&
                    ipZero == lastIP[1] && ipZero == lastIP[2] &&
                    ipZero == lastIP[3] && ipZero == lastIP[4] &&
                    ipZero == lastIP[5] && ipZero == lastIP[6] && ipZero == lastIP[7]) {
                REPORT_DEAD(cur_ctxt_hndl, ipZero, myhash, 8);
                // No state update needed
            } else {
                // slow path
                // byte 1 dead?
                REPORT_IF_DEAD(0x00000000000000ff, cur_ctxt_hndl, ipZero, myhash);
                // byte 2 dead?
                REPORT_IF_DEAD(0x000000000000ff00, cur_ctxt_hndl, lastIP[1], myhash);
                // byte 3 dead?
                REPORT_IF_DEAD(0x0000000000ff0000, cur_ctxt_hndl, lastIP[2], myhash);
                // byte 4 dead?
                REPORT_IF_DEAD(0x00000000ff000000, cur_ctxt_hndl, lastIP[3], myhash);
                // byte 5 dead?
                REPORT_IF_DEAD(0x000000ff00000000, cur_ctxt_hndl, lastIP[4], myhash);
                // byte 6 dead?
                REPORT_IF_DEAD(0x0000ff0000000000, cur_ctxt_hndl, lastIP[5], myhash);
                // byte 7 dead?
                REPORT_IF_DEAD(0x00ff000000000000, cur_ctxt_hndl, lastIP[6], myhash);
                // byte 8 dead?
                REPORT_IF_DEAD(0xff00000000000000, cur_ctxt_hndl, lastIP[7], myhash);
                // update state of these 8 bytes could be some overwrites
                *((uint64_t*)(status + PAGE_OFFSET((uint64_t)addr))) = EIGHT_BYTE_WRITE_ACTION;
            }
        } else {
            // update state of these 8 bytes
            *((uint64_t*)(status + PAGE_OFFSET((uint64_t)addr))) = EIGHT_BYTE_WRITE_ACTION;
        }
        state = (*((uint16_t*)(status + PAGE_OFFSET((uint64_t)addr) + 8)));

        if (state != TWO_BYTE_READ_ACTION) {
            DECLARE_HASHVAR(myhash);
            uint32_t ipZero = lastIP[8];

            // fast path where all bytes are dead by the same context
            if (state == TWO_BYTE_WRITE_ACTION && ipZero == lastIP[9]) {
                REPORT_DEAD(cur_ctxt_hndl, ipZero, myhash, 2);
                // No state update needed
            } else {
                // slow path
                // byte 1 dead?
                REPORT_IF_DEAD(0x00ff, cur_ctxt_hndl, ipZero, myhash);
                // byte 2 dead?
                REPORT_IF_DEAD(0xff00, cur_ctxt_hndl, lastIP[9], myhash);
                // update state
                *((uint16_t*)(status + PAGE_OFFSET(((uint64_t)addr + 8)))) = TWO_BYTE_WRITE_ACTION;
            }
        } else {
            //update states of these 2 bytes
            *((uint16_t*)(status + PAGE_OFFSET(((uint64_t)addr + 8)))) = TWO_BYTE_WRITE_ACTION;
        }

        lastIP[0] = cur_ctxt_hndl;
        lastIP[1] = cur_ctxt_hndl;
        lastIP[2] = cur_ctxt_hndl;
        lastIP[3] = cur_ctxt_hndl;
        lastIP[4] = cur_ctxt_hndl;
        lastIP[5] = cur_ctxt_hndl;
        lastIP[6] = cur_ctxt_hndl;
        lastIP[7] = cur_ctxt_hndl;
        lastIP[8] = cur_ctxt_hndl;
        lastIP[9] = cur_ctxt_hndl;
    } else {
        for (int i = 0; i < 10; i++) {
            Record1ByteMemWrite(((char*)addr) + i, cur_ctxt_hndl);
        }
    }
}


void
Record16ByteMemRead(void *addr) {
    uint8_t *status = GetShadowBaseAddress(addr);
    int overflow = PAGE_OFFSET((uint64_t)addr) - (PAGE_OFFSET_MASK - 15);

    if (overflow <= 0) {
        if (status) {
            *((uint64_t*)(status + PAGE_OFFSET((uint64_t)addr))) = EIGHT_BYTE_WRITE_ACTION;
            *((uint64_t*)(status + PAGE_OFFSET(((uint64_t)addr + 8)))) = EIGHT_BYTE_WRITE_ACTION;
        }
    } else {
        // slow path
        Record8ByteMemRead(addr);
        Record8ByteMemRead((char*)addr + 8);
    }
}


void
Record16ByteMemWrite(void *addr, context_handle_t cur_ctxt_hndl) {
    uint8_t *status = GetOrCreateShadowBaseAddress(addr);

    if (PAGE_OFFSET((uint64_t)addr) < (PAGE_OFFSET_MASK - 14)) {
        uint32_t *lastIP = (uint32_t*)(status + PAGE_SIZE + PAGE_OFFSET((uint64_t)addr) * sizeof(uint32_t));
        uint64_t state = *((uint64_t*)(status + PAGE_OFFSET((uint64_t)addr)));

        if (state != EIGHT_BYTE_READ_ACTION) {
            DECLARE_HASHVAR(myhash);
            uint32_t ipZero = lastIP[0];

            // fast path where all bytes are dead by the same context
            if (state == EIGHT_BYTE_WRITE_ACTION &&
                    ipZero == lastIP[1] && ipZero == lastIP[2] &&
                    ipZero == lastIP[3] && ipZero == lastIP[4] &&
                    ipZero == lastIP[5] && ipZero == lastIP[6] && ipZero == lastIP[7]) {
                REPORT_DEAD(cur_ctxt_hndl, ipZero, myhash, 8);
                // No state update needed
            } else {
                // slow path
                // byte 1 dead?
                REPORT_IF_DEAD(0x00000000000000ff, cur_ctxt_hndl, ipZero, myhash);
                // byte 2 dead?
                REPORT_IF_DEAD(0x000000000000ff00, cur_ctxt_hndl, lastIP[1], myhash);
                // byte 3 dead?
                REPORT_IF_DEAD(0x0000000000ff0000, cur_ctxt_hndl, lastIP[2], myhash);
                // byte 4 dead?
                REPORT_IF_DEAD(0x00000000ff000000, cur_ctxt_hndl, lastIP[3], myhash);
                // byte 5 dead?
                REPORT_IF_DEAD(0x000000ff00000000, cur_ctxt_hndl, lastIP[4], myhash);
                // byte 6 dead?
                REPORT_IF_DEAD(0x0000ff0000000000, cur_ctxt_hndl, lastIP[5], myhash);
                // byte 7 dead?
                REPORT_IF_DEAD(0x00ff000000000000, cur_ctxt_hndl, lastIP[6], myhash);
                // byte 8 dead?
                REPORT_IF_DEAD(0xff00000000000000, cur_ctxt_hndl, lastIP[7], myhash);
                // update state of these 8 bytes could be overwrites
                *((uint64_t*)(status + PAGE_OFFSET((uint64_t)addr))) = EIGHT_BYTE_WRITE_ACTION;
            }
        } else {
            // update state of these 8 bytes
            *((uint64_t*)(status + PAGE_OFFSET((uint64_t)addr))) = EIGHT_BYTE_WRITE_ACTION;
        }
        state = *((uint64_t*)(status + PAGE_OFFSET((uint64_t)addr) + 8)); 
        
        if (state != EIGHT_BYTE_READ_ACTION) {
            DECLARE_HASHVAR(myhash);
            uint32_t ipZero = lastIP[8];

            // fast path where all bytes are dead by the same context
            if (state == EIGHT_BYTE_WRITE_ACTION &&
                    ipZero == lastIP[9] && ipZero == lastIP[10] &&
                    ipZero == lastIP[11] && ipZero == lastIP[12] &&
                    ipZero == lastIP[13] && ipZero == lastIP[14] && ipZero == lastIP[15]) {
                REPORT_DEAD(cur_ctxt_hndl, ipZero, myhash, 8);
                // No state update needed
            } else {    
            // slow path
            // byte 1 dead?
            REPORT_IF_DEAD(0x00000000000000ff, cur_ctxt_hndl, ipZero, myhash);
            // byte 2 dead?
            REPORT_IF_DEAD(0x000000000000ff00, cur_ctxt_hndl, lastIP[9], myhash);
            // byte 3 dead?
            REPORT_IF_DEAD(0x0000000000ff0000, cur_ctxt_hndl, lastIP[10], myhash);
            // byte 4 dead?
            REPORT_IF_DEAD(0x00000000ff000000, cur_ctxt_hndl, lastIP[11], myhash);
            // byte 5 dead?
            REPORT_IF_DEAD(0x000000ff00000000, cur_ctxt_hndl, lastIP[12], myhash);
            // byte 6 dead?
            REPORT_IF_DEAD(0x0000ff0000000000, cur_ctxt_hndl, lastIP[13], myhash);
            // byte 7 dead?
            REPORT_IF_DEAD(0x00ff000000000000, cur_ctxt_hndl, lastIP[14], myhash);
            // byte 8 dead?
            REPORT_IF_DEAD(0xff00000000000000, cur_ctxt_hndl, lastIP[15], myhash);
            // update state 
            *((uint64_t*)(status + PAGE_OFFSET(((uint64_t)addr + 8)))) = EIGHT_BYTE_READ_ACTION;
            }
        } else{
            // update all 8 bytes status
            *((uint64_t*)(status + PAGE_OFFSET(((uint64_t)addr + 8)))) = EIGHT_BYTE_READ_ACTION;
        }

        lastIP[0] = cur_ctxt_hndl;
        lastIP[1] = cur_ctxt_hndl;
        lastIP[2] = cur_ctxt_hndl;
        lastIP[3] = cur_ctxt_hndl;
        lastIP[4] = cur_ctxt_hndl;
        lastIP[5] = cur_ctxt_hndl;
        lastIP[6] = cur_ctxt_hndl;
        lastIP[7] = cur_ctxt_hndl;
        lastIP[8] = cur_ctxt_hndl;
        lastIP[9] = cur_ctxt_hndl;
        lastIP[10] = cur_ctxt_hndl;
        lastIP[11] = cur_ctxt_hndl;
        lastIP[12] = cur_ctxt_hndl;
        lastIP[13] = cur_ctxt_hndl;
        lastIP[14] = cur_ctxt_hndl;
        lastIP[15] = cur_ctxt_hndl;
    } else {
        for (int i = 0; i < 16; i++) {
            Record1ByteMemWrite(((char*)addr) + i, cur_ctxt_hndl);
        }
    }
}


void
RecordLargeMemRead(void *addr, int size) {
    for (int i = 0; i < size; i++) {
        uint8_t *status = GetShadowBaseAddress(((char*)addr) + i);

        if (status) {
            *(status + PAGE_OFFSET(((uint64_t)addr + i))) = ONE_BYTE_READ_ACTION;
        }
    }
}


void
RecordLargeMemWrite(void *addr, context_handle_t cur_ctxt_hndl, int size) {
    for (int i = 0; i < size; i++) {
        // report dead for first byte if needed
        Record10ByteMemWrite((char*)addr + i, cur_ctxt_hndl);
    }
}


// client want to do
void
DoWhatClientWantTodo(void *drcontext, context_handle_t cur_ctxt_hndl, mem_ref_t *ref, int32_t op)
{
    // add online analysis here
    void *addr = ref->addr;
    int size = ref->size;
    //dr_fprintf(gTraceFile, "size is %d\n", size);
    
    //dr_fprintf(gTraceFile, "switch starts\n");

    switch (size){
    case 1:{
        //dr_fprintf(gTraceFile, "case1 starts\n");
	    if (op == 0){
            Record1ByteMemRead(addr);
        }
        if (op == 1){
            Record1ByteMemWrite(addr, cur_ctxt_hndl);
            //dr_fprintf(gTraceFile, "op == 1 Run\n");
        }
    }
    break;

    case 2:{
        if (op == 0){
            Record2ByteMemRead(addr);
	    }
	    if (op == 1) {
            Record2ByteMemWrite(addr, cur_ctxt_hndl);
        }
    }
    break;

    case 4:{
        if (op == 0) {
            Record4ByteMemRead(addr);
            //dr_fprintf(gTraceFile, "Run\n");
            //dr_fprintf(gTraceFile, "Dump Here\n");
	    }
        if (op == 1) {
            Record4ByteMemWrite(addr, cur_ctxt_hndl);
        }
    }
    break;

    case 8: {
        if (op == 0) {
	        Record8ByteMemRead(addr);
	    }
	    if (op == 1) {
	        Record8ByteMemWrite(addr, cur_ctxt_hndl);
	    }
    }
    break;

    case 10: {
	    if (op == 0){
	        Record10ByteMemRead(addr);
        }
	    if (op == 1) {
	        Record10ByteMemWrite(addr, cur_ctxt_hndl);
	    }
    }
    break;

    case 16: {
        if (op == 0) {
	        Record16ByteMemRead(addr);
            //r_fprintf(gTraceFile, "Run here\n");
	    }
	    if (op == 1) {
	        Record16ByteMemWrite(addr, cur_ctxt_hndl);
	    }
    }
    break;

    default: {
        if (op == 0) {
	        RecordLargeMemRead(addr, size);
	    }
	    if (op == 1) {
	        RecordLargeMemWrite(addr, cur_ctxt_hndl, size);
	    }
    }
    break;
    }//switch
    
}

// dr clean call
void
InsertCleancall(int32_t slot, int32_t num, int32_t op)
{
    void *drcontext = dr_get_current_drcontext();
    per_thread_t *pt = (per_thread_t *)drmgr_get_tls_field(drcontext, tls_idx);
    context_handle_t cur_ctxt_hndl = drcctlib_get_context_handle(drcontext, slot);
    for (int i = 0; i < num; i++) {
        if (pt->cur_buf_list[i].addr != 0) {
	    //if (cur_ctxt_hndl == 0) {
	        //DRCCTLIB_PRINTF("========");}
            DoWhatClientWantTodo(drcontext, cur_ctxt_hndl, &pt->cur_buf_list[i], op);
        }
    }
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
    int op = 0; // read is 0, write is 1
    for (int i = 0; i < instr_num_srcs(instr); i++) {
        if (opnd_is_memory_reference(instr_get_src(instr, i))) {
            num++;
            InstrumentMem(drcontext, bb, instr, instr_get_src(instr, i));
        }
    }
    dr_insert_clean_call(drcontext, bb, instr, (void *)InsertCleancall, false, 3,
                         OPND_CREATE_CCT_INT(slot), OPND_CREATE_CCT_INT(num), OPND_CREATE_CCT_INT(op));
    for (int i = 0; i < instr_num_dsts(instr); i++) {
        if (opnd_is_memory_reference(instr_get_dst(instr, i))) {
            num++;
	    op = 1;
            InstrumentMem(drcontext, bb, instr, instr_get_dst(instr, i));
        }
    }

#ifdef x86_CCTLIB
    if (drreg_unreserve_aflags(drcontext, bb, instr) != DRREG_SUCCESS) {
         DRCCTLIB_EXIT_PROCESS("drreg_unreserve_aflags != DRREG_SUCCESS");
    }
#endif

    dr_insert_clean_call(drcontext, bb, instr, (void *)InsertCleancall, false, 3,
                         OPND_CREATE_CCT_INT(slot), OPND_CREATE_CCT_INT(num), OPND_CREATE_CCT_INT(op));
}

static void
ClientThreadStart(void *drcontext)
{   
    // jtan
    // get thread number
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
    //PrintTopN(pt, OUTPUT_SIZE);
    dr_fprintf(gTraceFile, "ThreadEnd\n");
    dr_global_free(pt->cur_buf_list, TLS_MEM_REF_BUFF_SIZE * sizeof(mem_ref_t));
    dr_thread_free(drcontext, pt, sizeof(per_thread_t));
}

static void
ClientInit(int argc, const char *argv[])
{
    char name[MAXIMUM_PATH] = "";
    DRCCTLIB_INIT_LOG_FILE_NAME(name, "dead", "out");
    
    gTraceFile = dr_open_file(name, DR_FILE_WRITE_OVERWRITE | DR_FILE_ALLOW_LARGE);
    DR_ASSERT(gTraceFile != INVALID_FILE);
    dr_fprintf(gTraceFile, "ClientInit\n");   
}


// return the total N-byte size writes across all CCTs
uint64_t GetTotalNByteWrites() {
    uint64_t total = 0;
    // TODO
    return total;
}


uint64_t GetMeasurementBaseCount() {
    // byte count
    // uint64_t measurementBaseCount; 
    return 0;
}

// Print calling context of a given DeadInfo
void
PrintIPAndCallingContexts(const DeadInfoForPresentation &di) {
    dr_fprintf(gTraceFile, "di.count is: %lu\n", di.count);
    dr_fprintf(gTraceFile, "--------------------------------\n");
    drcctlib_print_backtrace(gTraceFile, di.pMergedDeadInfo->context1, true, true, -1);
    dr_fprintf(gTraceFile, "***************\n");
    drcctlib_print_backtrace(gTraceFile, di.pMergedDeadInfo->context2, true, true, -1);
    dr_fprintf(gTraceFile, "--------------------------------\n");
}

bool
MergedDeadInfoComparer(const DeadInfoForPresentation &first, const DeadInfoForPresentation &second) {
    // return true if the given deadinfo belongs to one of the loaded binaries
    /*
    bool tmp = first.count > second.count ? true : false;
    dr_fprintf(gTraceFile, "bool: %d\n", tmp);
    return tmp;
    */
    return first.count > second.count ? true : false;
}


static void
ClientExit(void)
{
    // On program termination output all data and statistics

    //unordered_map<uint64_t, uint64_t>::iterator mapIt = DeadMap.begin();
    auto mapIt = DeadMap.begin();
    map<MergedDeadInfo, uint64_t> mergedDeadInfoMap;

    for (; mapIt != DeadMap.end(); mapIt++) {
        MergedDeadInfo tmpMergedDeadInfo;
	    uint64_t hash = mapIt->first;
	    uint32_t ctxt1 = (hash >> 32);
	    uint32_t ctxt2 = (hash & 0xffffffff);
	    tmpMergedDeadInfo.context1 = ctxt1; // old
	    tmpMergedDeadInfo.context2 = ctxt2; // cur

        //dr_fprintf(gTraceFile, "hashVar: %lu\n", mapIt->first);
        /*
        dr_fprintf(gTraceFile, "context1: %u\n", ctxt1);
        dr_fprintf(gTraceFile, "context2: %u\n", ctxt2);
        dr_fprintf(gTraceFile, "size: %lu\n", mapIt->second);
        dr_fprintf(gTraceFile, "====================\n");
        */

        map<MergedDeadInfo, uint64_t>::iterator tmpIt;

        if ((tmpIt = mergedDeadInfoMap.find(tmpMergedDeadInfo)) == mergedDeadInfoMap.end()) {
            mergedDeadInfoMap[tmpMergedDeadInfo] = mapIt->second;
        } else {
            tmpIt->second += mapIt->second;
        }

	    //drcctlib_get_full_cct(context_handle_t ctxt_hndl, int max_depth);
	    
        /*
        if (ctxt1 == 0) {
	        dr_fprintf(gTraceFile, "context 1 is 0\n");
	    } else {
	        drcctlib_print_full_cct(gTraceFile, ctxt1, true, false, -1);
            dr_fprintf(gTraceFile, "=====================================\n");
	    }

	    drcctlib_print_full_cct(gTraceFile, MAX_CLIENT_CCT_PRINT_DEPTH);
        */
    }

    // clear dead map now
    DeadMap.clear();
    map<MergedDeadInfo, uint64_t>::iterator it = mergedDeadInfoMap.begin();
    list<DeadInfoForPresentation> deadList;

    for (; it != mergedDeadInfoMap.end(); it++) {
        DeadInfoForPresentation deadInfoForPresentation;
        deadInfoForPresentation.pMergedDeadInfo = &(it->first);
        deadInfoForPresentation.count = it->second;
        deadList.push_back(deadInfoForPresentation);
        //dr_fprintf(gTraceFile, "deadInfoForPresentation\n");
    }
    
    deadList.sort(MergedDeadInfoComparer);
    list<DeadInfoForPresentation>::iterator dipIter = deadList.begin();
    //PIN_LockClient();
    uint64_t deads = 0;

    for (; dipIter != deadList.end(); dipIter++) {
        //print MAX_DEAD_CONTEXTS_TO_LOG contexts
        if (deads < MAX_DEAD_CONTEXTS_TO_LOG) {
            // TODO
            PrintIPAndCallingContexts(*dipIter);
        }
        gTotalDead += dipIter->count;
        deads++;
    }

    dr_fprintf(gTraceFile, "ClientExit\n");
    uint64_t measurementBaseCount = 1.09;
    dr_fprintf(gTraceFile, "#deads\n");
    dr_fprintf(gTraceFile, "GrandTotalWrites = %d\n", measurementBaseCount);
    
    mergedDeadInfoMap.clear();
    deadList.clear();

    // PIN_UnlockClient();
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
