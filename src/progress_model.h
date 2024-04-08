#pragma once
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#define MAX_THREADS 2

int check_lock = 0;


typedef enum{
    STEP_LOAD,
    STEP_STORE,
    STEP_SUBGROUP_BARRIER,
    STEP_ATOMIC_EXCHANGE,
    STEP_LOCK_ACQUIRE,
    STEP_LOCK_RELEASE,
} step;

typedef struct Label{
    int id;
    int subgroup_id;
} Label;

typedef struct Thread{
    //Label metadata;
    step* instructions;
    int instruction_count;
    int pc;
    bool terminated;

} Thread;

typedef struct Subgroup{
    Thread threads[4];
    int thread_count;
} Subgroup;



typedef struct Scheduler{
    Thread* threads; // Dynamic array of Thread structures
    int thread_count; // Number of threads managed by the scheduler
    unsigned int fair_execution_bits; // Bit vector to track fair execution
    int terminated_thread_counts; // Number of threads that have terminated
    unsigned int unfair_thread_bits; // Bit vector to track unfair threads
} Scheduler;



int nondet_int();

step nondet_step(); // generate a non-deterministic step

bool nondet_bool();


bool fair_execution_set_contains(Scheduler* scheduler, int thread_id){
    return scheduler->fair_execution_bits & (1 << thread_id);
}

void fair_execution_set_insert(Scheduler* scheduler, int executed_thread_id){

   if (fair_execution_set_contains(scheduler, executed_thread_id)){
       return;
   }
    scheduler->fair_execution_bits |= 1 << executed_thread_id;

}

void fair_execution_set_remove(Scheduler* scheduler, int thread_id){
   if (fair_execution_set_contains(scheduler, thread_id)){
        scheduler->fair_execution_bits &= ~(1 << thread_id);
   }
}


bool fair_execution_set_is_empty(Scheduler* scheduler){
    //return scheduler->fair_count == 0;
    return scheduler->fair_execution_bits == 0;
}

int fair_execution_set_lowest_id(Scheduler* scheduler){

    for (int i = 0; i < scheduler->thread_count; ++i){
        if (scheduler->fair_execution_bits & (1 << i)){
            return i;
        }
    }
    return -1;
}
bool all_threads_terminated(Scheduler* scheduler){
    return scheduler->terminated_thread_counts == scheduler->thread_count;
}

bool unfair_thread_set_contains(Scheduler* scheduler, int thread_id){
    return scheduler->unfair_thread_bits & (1 << thread_id);
}

void unfair_thread_set_insert(Scheduler* scheduler, int thread_id){
    if (unfair_thread_set_contains(scheduler, thread_id)){
        return;
    }
    scheduler->unfair_thread_bits |= 1 << thread_id;
}

void unfair_thread_set_remove(Scheduler* scheduler, int thread_id){
    if (unfair_thread_set_contains(scheduler, thread_id)){
        scheduler->unfair_thread_bits &= ~(1 << thread_id);
    }
}


bool unfair_thread_set_is_empty(Scheduler* scheduler){
    return scheduler->unfair_thread_bits == 0;
}




void load(int threadidx, Scheduler* scheduler){
    //__CPROVER_assume(threadidx < MAX_THREADS);
    scheduler->threads[threadidx].pc += 1;

}


void atomic_exchange(int check_val, int jump_inst, bool do_exchange, int exch_val, int threadidx, Scheduler* scheduler){
    // insert the thread to the unfair thread set if lock is occupied and the thread is not in the unfair thread set
    if (check_lock == check_val && check_val == 1){
        if(!fair_execution_set_contains(scheduler, threadidx)){
            unfair_thread_set_insert(scheduler, threadidx);
        }
    }
    scheduler->threads[threadidx].pc = (check_lock == check_val) ? jump_inst : scheduler->threads[threadidx].pc + 1;
    if (do_exchange){
        check_lock = exch_val;
    }
}

void acquire(int threadidx, Scheduler* scheduler){
    int pc = scheduler->threads[threadidx].pc;
    // if acquire is unsuccessful, do not increment the pc
    atomic_exchange(1, pc, true, 1, threadidx, scheduler);
}

void release(int threadidx, Scheduler* scheduler){
    int pc = scheduler->threads[threadidx].pc + 1;
    // release always successful
    atomic_exchange(0, pc, true, 0, threadidx, scheduler);
    
}


void hsa_execute_step(Scheduler* scheduler, int thread_id){
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
            thread->pc += 1;
            break;
        case STEP_SUBGROUP_BARRIER:
            // todo
            break;
        case STEP_ATOMIC_EXCHANGE:
            int check_val = nondet_int();
            int jump_inst = nondet_int();
            bool do_exchange = nondet_int();
            int exch_val = nondet_int();
            // 1 = acquire, 0 = release
            __CPROVER_assume((check_val == 1 && exch_val == 1 && jump_inst == 0) || (check_val == 0 && exch_val == 0 && jump_inst == 2));
            atomic_exchange(check_val, jump_inst, do_exchange, exch_val, thread_id, scheduler);
            break;
        case STEP_LOCK_ACQUIRE:
            acquire(thread_id, scheduler);
            break;
        case STEP_LOCK_RELEASE:
            release(thread_id, scheduler);
            break;
        default:
            break;
    }
    


    // check if thread has terminated, and remove from fair execution set
    if (thread->pc == thread->instruction_count){
        thread->terminated = true;
        scheduler->terminated_thread_counts += 1;
        //scheduler->terminated_threads |= 1 << thread_id;
        if (fair_execution_set_contains(scheduler, thread_id)){
            fair_execution_set_remove(scheduler, thread_id);
           // unfair_thread_set_remove(scheduler, thread_id);
        }
    }
    // insert to the fair execution set if is the lowest thread id
    if (thread->terminated == false){
        int lowest_id = fair_execution_set_lowest_id(scheduler);
        // no thread in the fair execution set, insert the current thread
        if (lowest_id == -1){
            fair_execution_set_insert(scheduler, thread_id);
            unfair_thread_set_remove(scheduler, thread_id);
            
        }
        // insert the current thread if it has the lowest id
        // add the lowest id thread to the unfair thread set
        else if (lowest_id > thread_id){
            fair_execution_set_remove(scheduler, lowest_id);
            unfair_thread_set_insert(scheduler, lowest_id);
            fair_execution_set_insert(scheduler, thread_id);
            unfair_thread_set_remove(scheduler, thread_id);
        }
    }
}



void obe_execute_step(Scheduler* scheduler, int thread_id){
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
            thread->pc += 1;
            // todo
            break;
        case STEP_SUBGROUP_BARRIER:
            // todo
            break;
        case STEP_ATOMIC_EXCHANGE:
            int check_val = nondet_int();
            int jump_inst = nondet_int();
            bool do_exchange = true;
            int exch_val = nondet_int();
            // 1 = acquire, 0 = release
            __CPROVER_assume((check_val == 1 && exch_val == 1 && jump_inst == 0) || (check_val == 0 && exch_val == 0 && jump_inst == 2));
            atomic_exchange(check_val, jump_inst, do_exchange, exch_val, thread_id, scheduler);
            break;
        case STEP_LOCK_ACQUIRE:
            acquire(thread_id, scheduler);
            break;
        case STEP_LOCK_RELEASE:
            release(thread_id, scheduler);
            break;
        default:
            break;
    }


    // check if thread has terminated, and remove from fair execution set
    if (thread->pc == thread->instruction_count){
        thread->terminated = true;
        scheduler->terminated_thread_counts += 1;
        fair_execution_set_remove(scheduler, thread_id);
    
    }
    // insert to the fair execution set as it made at least one execution step
    // also remove it from the unfair thread set
    if (thread->terminated == false && fair_execution_set_contains(scheduler, thread_id) == false){
        fair_execution_set_insert(scheduler, thread_id);
        unfair_thread_set_remove(scheduler, thread_id);
    }
}
