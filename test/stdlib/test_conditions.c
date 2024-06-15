#include <assert.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "macros.h"
#include "print.h"
#include "randombytes.h"
#include "utils.h"

#ifndef TESTS
#define TESTS 100000
#endif

extern uint8_t cond_u64_geq_u64_u32_eq_u32_jazz(uint64_t, uint64_t, uint32_t, uint32_t);

void test_cond_u64_geq_u64_u32_eq_u32(void) {
    for (int i = 0; i < TESTS; i++) {
        // TODO:
    }
}

int main(void) {
    puts("CONDITIONS : OK");
    return 0;
}