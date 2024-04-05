#include<assert.h>
#include <stdio.h>
#include "hsa.h"



int main() {
    
    for (;nondet_int();){
        int thread_id = nondet_int();
        __CPROVER_assume(thread_id >= 0 && thread_id < MAX_THREADS);
        switch (nondet_step()){
            case STEP_LOAD:
                printf("Load\n");
            break;
            default:
                printf("Default\n");
                break;
        }
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
    return 0;
}