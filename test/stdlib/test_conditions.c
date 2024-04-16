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
extern uint8_t cond_u32_geq_u32_u32_eq_u32_jazz(uint32_t, uint32_t, uint32_t, uint32_t);

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

void test_cond_u32_geq_u32_u32_eq_u32(void) {
    uint32_t a, b, c, d;
    uint8_t r;

    // 1) Random Bytes
    for (int i = 0; i < TESTS; i++) {
        randombytes((uint8_t *)&a, sizeof(uint32_t));
        randombytes((uint8_t *)&b, sizeof(uint32_t));
        randombytes((uint8_t *)&c, sizeof(uint32_t));
        randombytes((uint8_t *)&d, sizeof(uint32_t));

        r = cond_u32_geq_u32_u32_eq_u32_jazz(a, b, c, d);
        assert((a >= b && c == d) ? (r == 1) : (r == 0));
    }

    // 2) a >= b is true but c == d is false
    for (int i = 0; i < TESTS; i++) {
        // a) Case when a > b
        randombytes((uint8_t *)&a, sizeof(uint32_t));
        b = a - 1;

        randombytes((uint8_t *)&c, sizeof(uint32_t));
        d = c + 1;

        r = cond_u32_geq_u32_u32_eq_u32_jazz(a, b, c, d);
        assert((a >= b && c == d) ? (r == 1) : (r == 0));

        // b) Case when a == b
        randombytes((uint8_t *)&a, sizeof(uint32_t));
        b = a;

        randombytes((uint8_t *)&c, sizeof(uint32_t));
        d = c + 1;

        r = cond_u32_geq_u32_u32_eq_u32_jazz(a, b, c, d);
        assert((a >= b && c == d) ? (r == 1) : (r == 0));
    }

    // 3) c == d is true but a >= b is false
    for (int i = 0; i < TESTS; i++) {
        randombytes((uint8_t *)&a, sizeof(uint32_t));
        b = a + 1;

        randombytes((uint8_t *)&c, sizeof(uint32_t));
        d = c;

        r = cond_u32_geq_u32_u32_eq_u32_jazz(a, b, c, d);
        assert((a >= b && c == d) ? (r == 1) : (r == 0));
    }

    // a >= b and c == d are both false
    for (int i = 0; i < TESTS; i++) {
        randombytes((uint8_t *)&a, sizeof(uint32_t));
        b = a + 1;
        randombytes((uint8_t *)&c, sizeof(uint32_t));
        d = c + 1;

        r = cond_u32_geq_u32_u32_eq_u32_jazz(a, b, c, d);
        assert((a >= b && c == d) ? (r == 1) : (r == 0));
    }

    puts("cond_u32_geq_u32_u32_eq_u32: a >= b /\\ c == d OK");
}

int main(void) {
    test_cond_u32_a_below_b_and_a_below_c();
    test_cond_u32_geq_u32_u32_eq_u32();
    puts("CONDITIONS : OK");
    return 0;
}