#pragma once
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include "instruction.h"


typedef struct Scheduler{
    Thread* threads; // Dynamic array of Thread structures
    int thread_count; // Number of threads managed by the scheduler
    //int* fair_execution_set; // Dynamic array of thread IDs guaranteed fair execution
    //int fair_count; // Number of thread IDs in the fair execution set
    unsigned int fair_execution_bits; // Bit vector to track fair execution
} Scheduler;


// Assume OBE for new
void fair_execution_set_insert(Scheduler* scheduler, int executed_thread_id){
    /*
    if (scheduler->fair_count == scheduler->fair_capacity){
        // double the capacity of the fair execution set
        scheduler->fair_capacity *= 2;
        scheduler->fair_execution_set = (int*)realloc(scheduler->fair_execution_set, scheduler->fair_capacity * sizeof(int));
    }
    scheduler->fair_execution_set[scheduler->fair_count] = executed_thread_id;
    scheduler->fair_count += 1;
    */
    scheduler->fair_execution_bits |= 1 << executed_thread_id;

}

void fair_execution_set_remove(Scheduler* scheduler, int thread_id){
    /*
    int* new_fair_execution_set = (int*)malloc(scheduler->fair_capacity * sizeof(int));
    int new_fair_count = 0;
    for (int i = 0; i < scheduler->fair_count; ++i){
        if (scheduler->fair_execution_set[i] != thread_id){
            new_fair_execution_set[new_fair_count] = scheduler->fair_execution_set[i];
            new_fair_count += 1;
        }
    }
    free(scheduler->fair_execution_set);
    scheduler->fair_execution_set = new_fair_execution_set;
    scheduler->fair_count = new_fair_count;
    */
    scheduler->fair_execution_bits &= ~(1 << thread_id);
}

bool fair_execution_set_contains(Scheduler* scheduler, int thread_id){
    //for (int i = 0; i < scheduler->fair_count; ++i){
    //    if (scheduler->fair_execution_set[i] == thread_id){
    //        return true;
    //    }
    //}
    //return false;
    return scheduler->fair_execution_bits & (1 << thread_id);
}

bool fair_execution_set_is_empty(Scheduler* scheduler){
    //return scheduler->fair_count == 0;
    return scheduler->fair_execution_bits == 0;
}

int fair_execution_set_lowest_id(Scheduler* scheduler){
    //int lowest_id = scheduler->fair_execution_set[0];
    //for (int i = 1; i < scheduler->fair_count; ++i){
    //    if (scheduler->fair_execution_set[i] < lowest_id){
    //        lowest_id = scheduler->fair_execution_set[i];
    //    }
    //}
    //return lowest_id;
    for (int i = 0; i < scheduler->thread_count; ++i){
        if (scheduler->fair_execution_bits & (1 << i)){
            return i;
        }
    }
    return -1;
}

void execute_step(Scheduler* scheduler, int thread_id){
    Thread* thread = &scheduler->threads[thread_id];
    // do nothing to terminated thread
    if (thread->terminated){
        return;
    }
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
        case STEP_ATOMIC_EXCHANGE:
            // todo
            break;
        default:
            break;
    }
    
    // increment pc to next instruction
    thread->pc += 1;

    // check if thread has terminated, and remove from fair execution set
    if (thread->pc == thread->instruction_count){
        thread->terminated = true;
        if (fair_execution_set_contains(scheduler, thread_id)){
            fair_execution_set_remove(scheduler, thread_id);
        }
    }
    if (thread->terminated == false && fair_execution_set_contains(scheduler, thread_id) == false){
        fair_execution_set_insert(scheduler, thread_id);
    }
}