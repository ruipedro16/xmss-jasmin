#include <assert.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#ifndef IMPL
#error IMPL not defined
#endif

#ifndef MAX_MSG_LEN
#define MAX_MSG_LEN 1024
#endif

#ifndef TIMINGS
#define TIMINGS 10000
#endif

#ifndef LOOPS
#define LOOPS 1
#endif


int main(void) {
    bool debug = true;

    for (int i=0; i < 10; i++) {
        // warmup
    }

    // TODO:

    for(int loop = 0; loop < LOOPS; loop++) {
        for (size_t message_len = 1; message_len <= MAX_MSG_LEN; message_len++) {

        printf("[MessageLen=%ld]: Loop iteration: %d\n", message_len, loop);
        }
    }

    return 0;
}