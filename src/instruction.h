#pragma once
#include <time.h>
#include <stdlib.h>
#include <stdbool.h>
#define MAX_THREADS 2

int lock = -1;

typedef enum{
    STEP_LOAD,
    STEP_STORE,
    STEP_SUBGROUP_BARRIER,
    STEP_ATOMIC_EXCHANGE,
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


int nondet_int();

step nondet_step(); // generate a non-deterministic step



void acquire_lock(int threadidx){
    __CPROVER_assume(threadidx < MAX_THREADS);
    if (!locks[threadidx]){
        locks[threadidx] = true;
    }
}

// assume HSA
void atomic_exchange(int threadidx){
    _CPROVER_assume(threadidx < MAX_THREADS);

}