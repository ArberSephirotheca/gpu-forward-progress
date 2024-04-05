#include<assert.h>
#include <stdio.h>
#include "instruction.h"
#include "progress_model.h"


int main() {
    Scheduler scheduler = {};
    Thread thread1, thread2;
    step instructions1[] = {STEP_LOAD, STEP_STORE, STEP_SUBGROUP_BARRIER, STEP_ATOMIC_EXCHANGE};
    thread1.instructions = instructions1;
    thread1.instruction_count = 4;
    thread1.pc = 0;
    thread1.terminated = false;

    step instructions2[] = {STEP_LOAD, STEP_STORE, STEP_SUBGROUP_BARRIER, STEP_ATOMIC_EXCHANGE};
    thread2.instructions = instructions2;
    thread2.instruction_count = 4;
    thread2.pc = 0;
    thread2.terminated = false;

    Thread threads[] = {thread1, thread2};

    scheduler.threads = threads;
    scheduler.thread_count = 2;
    scheduler.fair_execution_bits = 0;
    

    for (;nondet_int();){
        int thread_id = nondet_int();
        __CPROVER_assume(thread_id >= 0 && thread_id < scheduler.thread_count);
        execute_step(&scheduler, thread_id);
    }
    /*

    // Spawn threads to simulate concurrent execution
    __CPROVER_ASYNC_1: thread_function(0);
    __CPROVER_ASYNC_2: thread_function(1);
    */
    // Verification conditions can include checking that all resources were eventually acquired
    //for(int i = 0; i < 2; ++i) {
       // assert(resource == false); // Ensure all resources are released at the end
    //}

    return EXIT_SUCCESS;
}