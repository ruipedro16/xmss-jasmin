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
    // Test case 1: a >= b and c == d (should return true)
    assert(cond_u64_geq_u64_u32_eq_u32_jazz(10, 10, 5, 5) == 1);
    assert(cond_u64_geq_u64_u32_eq_u32_jazz(20, 10, 5, 5) == 1);
    assert(cond_u64_geq_u64_u32_eq_u32_jazz(UINT64_MAX, UINT64_MAX, 0, 0) == 1);

    // Test case 2: a >= b and c != d (should return false)
    assert(cond_u64_geq_u64_u32_eq_u32_jazz(10, 10, 5, 4) == 0);
    assert(cond_u64_geq_u64_u32_eq_u32_jazz(20, 10, 5, 4) == 0);
    assert(cond_u64_geq_u64_u32_eq_u32_jazz(UINT64_MAX, UINT64_MAX, 0, 1) == 0);

    // Test case 3: a < b and c == d (should return false)
    assert(cond_u64_geq_u64_u32_eq_u32_jazz(10, 20, 5, 5) == 0);
    assert(cond_u64_geq_u64_u32_eq_u32_jazz(0, 1, 10, 10) == 0);
    assert(cond_u64_geq_u64_u32_eq_u32_jazz(123456789, 987654321, 12345, 12345) == 0);

    // Test case 4: a < b and c != d (should return false)
    assert(cond_u64_geq_u64_u32_eq_u32_jazz(10, 20, 5, 4) == 0);
    assert(cond_u64_geq_u64_u32_eq_u32_jazz(0, 1, 10, 9) == 0);
    assert(cond_u64_geq_u64_u32_eq_u32_jazz(123456789, 987654321, 12345, 54321) == 0);

    uint64_t a, b;
    uint32_t c, d;
    uint64_t temp;

    // Test case 1: a >= b and c == d (should return true)
    for (int i = 0; i < TESTS; ++i) {
        randombytes((uint8_t *)&a, sizeof(uint64_t));
        randombytes((uint8_t *)&b, sizeof(uint64_t));

        if (a < b) {
            temp = a;
            a = b;
            b = temp;
        }

        randombytes((uint8_t *)&c, sizeof(uint32_t));
        d = c;  // Ensuring c == d

        assert(cond_u64_geq_u64_u32_eq_u32_jazz(a, b, c, d) == 1);
    }

    // Test case 2: a >= b and c != d (should return false)
    for (int i = 0; i < TESTS; ++i) {
        randombytes((uint8_t *)&a, sizeof(uint64_t));
        randombytes((uint8_t *)&b, sizeof(uint64_t));

        if (a < b) {
            temp = a;
            a = b;
            b = temp;
        }

        randombytes((uint8_t *)&c, sizeof(uint32_t));
        d = c + 1;  // Ensuring c != d

        assert(cond_u64_geq_u64_u32_eq_u32_jazz(a, b, c, d) == 0);
    }

    // Test case 3: a < b and c == d (should return false)
    for (int i = 0; i < TESTS; ++i) {
        randombytes((uint8_t *)&a, sizeof(uint64_t));
        randombytes((uint8_t *)&b, sizeof(uint64_t));

        if (a >= b) {
            temp = a;
            a = b;
            b = temp + 1;  // Ensure a < b
        }

        randombytes((uint8_t *)&c, sizeof(uint32_t));
        d = c;  // Ensuring c == d

        assert(cond_u64_geq_u64_u32_eq_u32_jazz(a, b, c, d) == 0);
    }

    // Test case 4: a < b and c != d (should return false)
    for (int i = 0; i < TESTS; ++i) {
        randombytes((uint8_t *)&a, sizeof(uint64_t));
        randombytes((uint8_t *)&b, sizeof(uint64_t));

        if (a >= b) {
            temp = a;
            a = b;
            b = temp + 1;  // Ensure a < b
        }

        randombytes((uint8_t *)&c, sizeof(uint32_t));
        d = c + 1;  // Ensuring c != d

        assert(cond_u64_geq_u64_u32_eq_u32_jazz(a, b, c, d) == 0);
    }
}

int main(void) {
    test_cond_u64_geq_u64_u32_eq_u32();
    puts("CONDITIONS : OK");
    return 0;
}