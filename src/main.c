#include<assert.h>
#include <stdio.h>
#include "progress_model.h"


int main() {
    Scheduler scheduler = {};
    Thread thread1, thread2;
    step instructions1[] = {STEP_LOCK_ACQUIRE, STEP_STORE, STEP_LOCK_RELEASE};
    thread1.instructions = instructions1;
    thread1.instruction_count = 3;
    thread1.pc = 0;
    thread1.terminated = false;

    step instructions2[] = {STEP_LOCK_ACQUIRE, STEP_STORE, STEP_LOCK_RELEASE};
    thread2.instructions = instructions2;
    thread2.instruction_count = 3;
    thread2.pc = 0;
    thread2.terminated = false;

    Thread threads[] = {thread1, thread2};

    scheduler.threads = threads;
    scheduler.thread_count = 2;
    scheduler.fair_execution_bits = 0;
    scheduler.terminated_thread_counts = 0;
    scheduler.unfair_thread_bits = 0;
    
    int num_steps = nondet_int();
    __CPROVER_assume(num_steps > thread1.instruction_count + thread2.instruction_count);
    for(int i = 0; i < num_steps; ++ i){
        int thread_id = nondet_int();
        // resricting thread_id to be within the range of thread_count and not terminated
        __CPROVER_assume(thread_id >= 0 && thread_id < scheduler.thread_count && scheduler.threads[thread_id].terminated == false);
        //hsa_execute_step(&scheduler, thread_id);
        obe_execute_step(&scheduler, thread_id);
    }
    // deadlock
    __CPROVER_assert(scheduler.unfair_thread_bits == 0, "Deadlock detected");
    // livelock
    __CPROVER_assert(scheduler.terminated_thread_counts == scheduler.thread_count, "Livelock detected");
    return EXIT_SUCCESS;
}