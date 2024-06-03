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

extern uint8_t cond_u32_a_below_b_and_a_below_c_jazz(uint32_t, uint32_t, uint32_t);

void test_cond_u32_a_below_b_and_a_below_c(void) {
    uint32_t a, b, c;
    uint8_t r;

    for (int i = 0; i < TESTS; i++) {
        randombytes((uint8_t *)&a, sizeof(uint32_t));
        randombytes((uint8_t *)&b, sizeof(uint32_t));
        randombytes((uint8_t *)&c, sizeof(uint32_t));

        r = cond_u32_a_below_b_and_a_below_c_jazz(a, b, c);
        assert((a < b && a < c) ? (r == 1) : (r == 0));
    }

    // TODO: More tests

    puts("cond_u32_a_below_b_and_a_below_c: a < b /\\ a < c OK");
}

int main(void) {
    test_cond_u32_a_below_b_and_a_below_c();
    puts("CONDITIONS : OK");
    return 0;
}