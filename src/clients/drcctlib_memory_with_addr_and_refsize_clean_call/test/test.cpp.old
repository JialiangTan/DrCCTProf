#include <stdio.h>
#include <stdlib.h>
#include <map>
#include <string>
#include <iostream>
#include <unistd.h>

#include "dr_api.h"
#include "drmgr.h"
#include "drcctlib.h"

using namespace tsd;

//R, W representative macros
#define READ_ACTION (0)
#define WRITE_ACTION (0xff)

#define ONE_BYTE_READ_ACTION (0)
#define TWO_BYTE_READ_ACTION (0)
#define FOUR_BYTE_READ_ACTION (0)
#define EIGHT_BYTE_READ_ACTION (0)

#define ONE_BYTE_WRITE_ACTION (0xff)
#define TWO_BYTE_WRITE_ACTION (0xffff)
#define FOUR_BYTE_WRITE_ACTION (0xffffffff)
#define EIGHT_BYTE_WRITE_ACTION (0xffffffffffffffff)







// Is called for every instruction
void
InstrumentInsCallback(void *drcontext, instr_instrument_msg_t *instrument_msg){
    instrlist_t *bb = instrument_msg->bb;
    instr_t *instr = instrument_msg->instr;
    
    // How many memory operands?
    // Returns the number of source operands of instr.
    uint32 memOperands = instr_num_srcs(instr);

    for (uint32 memOp = 0; memOp < memOperands; memOp++){
        // Calculates the size, in bytes, of the memory read or write of instr.
        // instr_memory_reference_size();
	uint32 refSize = instr_memory_reference_size(instr);
        //Returns true iff any of instr's source operands is a memory reference.
        // instr_reads_memory();
	switch(refSize){
	case 1: {
	    if(instr_reads_memory(intr)){
	        INS_InsertPredicatedCall();//TODO
	    }
            if(instr_writes_memory(intr)){
	        INS_InsertPredicatedCall();//TODO
	    }
	}
	break;
	
	case 2: {
	    if(instr_reads_memory(intr)){
	        INS_InsertPredicatedCall();//TODO
	    }
            if(instr_writes_memory(intr)){
	        INS_InsertPredicatedCall();//TODO
	    }
	}
	break;
	
	case 4: {
	    if(instr_reads_memory(intr)){
	        INS_InsertPredicatedCall();//TODO
	    }
            if(instr_writes_memory(intr)){
	        INS_InsertPredicatedCall();//TODO
	    }
	}
	break;

	case 8: {
	    if(instr_reads_memory(intr)){
	        INS_InsertPredicatedCall();//TODO
	    }
            if(instr_writes_memory(intr)){
	        INS_InsertPredicatedCall();//TODO
	    }
	}
	break;

	case 10: {
	    if(instr_reads_memory(intr)){
	        INS_InsertPredicatedCall();//TODO
	    }
            if(instr_writes_memory(intr)){
	        INS_InsertPredicatedCall();//TODO
	    }
	}
	break;

	case 16: {
	    if(instr_reads_memory(intr)){
	        INS_InsertPredicatedCall();//TODO
	    }
            if(instr_writes_memory(intr)){
	        INS_InsertPredicatedCall();//TODO
	    }
	}
	break;

	default: {
	    if(instr_reads_memory(intr)){
	        INS_InsertPredicatedCall();//TODO
	    }
            if(instr_writes_memory(intr)){
	        INS_InsertPredicatedCall();//TODO
	    }
	}
	break;

	}//switch

    }//for
}//func

void
InstrumentPerBBCache(void *drcontext, context_handle_t ctxt_hndl, int32_t slot_num,
                     int32_t mem_ref_num, mem_ref_msg_t *mem_ref_start, void **data){

    //if (instr_writes_memory(*instr)){
    //}
}


void
Record1ByteMemRead(void* addr) {
    uint8_t* status = GetShadowBaseAddress(addr);

    // status == 0 if not created.
    if(status) {
        // NOT NEEDED status->lastIP = ip;
        *(status + PAGE_OFFSET((uint64_t)addr))  = ONE_BYTE_READ_ACTION;
    }
}

void
Record1ByteMemWrite(void *addr){
}

void
Record4ByteMemRead(void *addr){
}

void
Record4ByteMemWrite(void *addr){
}

void 
Record8ByteMemRead(void *addr){
}

void 
Record8ByteMemWrite(void *addr){
}

void 
Record10ByteMemRead(void *addr){
}

void
Record10ByteMemWrite(void *addr){
}

void 
Record16ByteMemRead(void *addr){
}

void
Record16ByteMemWrite(void *addr){
}

void 
RecordLargeMemRead(void *addr){
}

void
RecordLargeWrite(void *addr){
}



//static void
//ClientThreadStart(void *drcontext){
//}

//static void
//ClientThreadEnd(void *drcontext){
//}


static void
ClientInit(int argc, const char *argv[])
{
    char name[MAXIMUM_PATH] = "";
    DRCCTLIB_INIT_LOG_FILE_NAME(
        name, "drcctlib_reuse_distance", "out");
    g_folder_name.assign(name, strlen(name));
    mkdir(g_folder_name.c_str(), S_IRWXU | S_IRWXG | S_IROTH | S_IXOTH);
}

static void
ClientExit(void)
{
    drcctlib_exit();
    if (!drmgr_unregister_thread_init_event(ClientThreadStart) ||
        !drmgr_unregister_thread_exit_event(ClientThreadEnd) ||
        !drmgr_unregister_tls_field(tls_idx)) {
        DRCCTLIB_PRINTF(
            "ERROR: drcctlib_reuse_distance failed to unregister in ClientExit");
    }
    drmgr_exit();
}


DR_EXPORT void
dr_client_main(client_id_t id, int argc, const char *argv[]){
    //Set client name
    dr_set_client_name("DynamoRIO Client 'drcctlib_deadspy'", "http://dynamorio.org/issues");
    //Initialize
    ClientInit(argc, argv);

    if(!drmgr_init()){
        DRCCTLIB_EXIT_PROCESS("ERROR: drcctlib_deadspy unable to initialize drmgr");
    }

    //drmgr_register_thread_init_event_ex(ClientThreadStart, &thread_init_pri);
    //drmgr_register_thread_init_exit_ex(ClientThreadEnd, &thread_exit_pri);

    //tls_idx = drmgr_register_tls_field();
    //if(tls_idx == -1){
        //DRCCTLIB_EXIT_PROCESS("ERROR: drcctlib_deadspy drmgr_register_tls_field fail");
    //}
    drcctlib_init_ex(DRCCTLIB_FILTER_MEM_ACCESS_INSTR, INVALID_FILE,
                     InstrumentInsCallback, InstrumentPerBBCache, NULL,
		     DRCCTLIB_COLLECT_DATA_CENTRIC_MESSAGE | DRCCTLIB_CACHE_MODE | DRCCTLIB_CACHE_MEMEORY_ACCESS_ADDR);
    dr_register_exit_event(ClientExit);

}
