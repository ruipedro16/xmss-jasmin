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
#define TESTS 1000
#endif

#ifndef INLEN
#error INLEN not defined
#endif

#define bytes_to_ull_jazz NAMESPACE1(bytes_to_ull_jazz, INLEN)
extern uint64_t bytes_to_ull_jazz(const uint8_t *);

extern uint64_t bytes_to_ull_ptr_jazz(const uint8_t *, size_t);

void test_bytes_to_ull(void) {
    bool debug = true;

    uint8_t in[INLEN];
    uint64_t out_ref, out_jazz;

    for (int i = 0; i < TESTS; i++) {
        if (debug) {
            printf("[bytes_to_ull] Test %d/%d\n", i, TESTS);
        }

        randombytes(in, INLEN);
        out_ref = (uint64_t)bytes_to_ull(in, INLEN);
        out_jazz = bytes_to_ull_jazz(in);

        if (out_ref != out_jazz) {
            print_str_u8("ref", (uint8_t *)&out_ref, sizeof(uint64_t));
            print_str_u8("jazz", (uint8_t *)&out_jazz, sizeof(uint64_t));
        }

        assert(out_ref == out_jazz);
    }
}

void test_bytes_to_ull_ptr(void) {
    bool debug = true;

    uint8_t in[INLEN];
    uint64_t out_ref, out_jazz;

    for (int i = 0; i < TESTS; i++) {
        if (debug) {
            printf("[bytes_to_ull_ptr] Test %d/%d\n", i, TESTS);
        }

        randombytes(in, INLEN);
        out_ref = (uint64_t)bytes_to_ull(in, INLEN);
        out_jazz = bytes_to_ull_ptr_jazz(in, INLEN);

        if (out_ref != out_jazz) {
            print_str_u8("ref", (uint8_t *)&out_ref, sizeof(uint64_t));
            print_str_u8("jazz", (uint8_t *)&out_jazz, sizeof(uint64_t));
        }

        assert(out_ref == out_jazz);
    }
}

int main(void) {
    test_bytes_to_ull();
    test_bytes_to_ull_ptr();
    printf("Utils [INLEN=%d]: OK\n", INLEN);
    return 0;
}