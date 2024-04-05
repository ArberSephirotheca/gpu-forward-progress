#pragma once
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include "instruction.h"


typedef struct Scheduler{
    Thread* threads; // Dynamic array of Thread structures
    int thread_count; // Number of threads managed by the scheduler
    int* fair_execution_set; // Dynamic array of thread IDs guaranteed fair execution
    int fair_count; // Number of thread IDs in the fair execution set
} Scheduler;


void update_fair_execution_set(Scheduler* scheduler, int executed_thread_id){
    // unimplemented
}

void execute_step(Scheduler* scheduler, int thread_id){
    Thread* thread = &scheduler->threads[thread_id];
    // do nothing to terminated thread
    if (thread->terminated)
        return;
    step instruction = thread->instructions[thread->pc];
    switch (instruction){
        case STEP_LOAD:
            // todo
            break;
        case STEP_STORE:
            // todo
            break;
        case STEP_SUBGROUP_BARRIER:
            // todo
            break;
    }
    
    thread->pc += 1;

    if (thread->pc == thread->instruction_count){
        thread->terminated = true;
    }

    update_fair_execution_set(scheduler, thread_id);
}