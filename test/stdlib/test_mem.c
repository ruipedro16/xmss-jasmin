#include <assert.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "macros.h"
#include "params.h"
#include "print.h"
#include "randombytes.h"
#include "utils.h"

#ifndef TESTS
#define TESTS 1000
#endif

#ifndef IMPL
#error IMPL not defined
#endif

#ifndef MAX_BUFSIZE
#define MAX_BUFSIZE 1024
#endif

extern void memset_zero_u8_jazz(uint8_t *);
extern void memset_u8_ptr_jazz(uint8_t *, size_t, uint8_t);

extern int memcmp_jazz(const uint8_t *, const uint8_t *);

void test_memset_zero_u8(void) {
    bool debug = true;

    xmss_params p;
    uint32_t oid;

    if (xmss_str_to_oid(&oid, xstr(IMPL)) == -1) {
        fprintf(stderr, "Failed to generate oid from impl name\n");
        exit(-1);
    }

    if (xmss_parse_oid(&p, oid) == -1) {
        fprintf(stderr, "Failed to generate params from oid\n");
        exit(-1);
    }

    uint8_t buf[p.index_bytes];
    uint8_t zero_buf[p.index_bytes];

    memset(zero_buf, 0, p.index_bytes * sizeof(uint8_t));

    for (int i = 0; i < TESTS; i++) {
        if (debug) {
            printf("[memset_zero_u8] Test %d/%d\n", i + 1, TESTS);
        }

        randombytes(buf, p.index_bytes * sizeof(uint8_t));
        memset_zero_u8_jazz(buf);
        assert(memcmp(buf, zero_buf, p.index_bytes * sizeof(uint8_t)) == 0);
    }
}

void test_memset_u8_ptr(void) {
    bool debug = true;

    uint8_t buf[MAX_BUFSIZE];
    uint8_t val_buf[MAX_BUFSIZE];
    uint8_t val;

    for (size_t len = 1; len <= MAX_BUFSIZE; len++) {
        for (int i = 0; i < TESTS; i++) {
            if (debug) {
                printf("[memset_u8 (len=%ld)] Test %d/%d\n", len, i + 1, TESTS);
            }

            randombytes(&val, sizeof(uint8_t));
            memset(val_buf, val, len * sizeof(uint8_t));  // setup buffer for comparison

            memset_u8_ptr_jazz(buf, len, val);

            assert(memcmp(buf, val_buf, len * sizeof(uint8_t)) == 0);
        }
    }
}

void test_memcmp(void) {
    bool debug = true;

    xmss_params p;
    uint32_t oid;

    if (xmss_str_to_oid(&oid, xstr(IMPL)) == -1) {
        fprintf(stderr, "Failed to generate oid from impl name\n");
        exit(-1);
    }

    if (xmss_parse_oid(&p, oid) == -1) {
        fprintf(stderr, "Failed to generate params from oid\n");
        exit(-1);
    }

    uint8_t a[p.n];
    uint8_t b[p.n];
    int res;

    // a and b are random
    for (int i = 0; i < TESTS; i++) {
        if (debug) {
            printf("[memcmp 1] Test %d/%d\n", i + 1, TESTS);
        }

        randombytes(a, p.n * sizeof(uint8_t));
        randombytes(b, p.n * sizeof(uint8_t));

        res = memcmp_jazz(a, b);

        assert((memcmp(a, b, p.n * sizeof(uint8_t)) == 0) ? (res == 0) : (res == -1));
    }

    // a and b are equal
    for (int i = 0; i < TESTS; i++) {
        if (debug) {
            printf("[memcmp 2] Test %d/%d\n", i + 1, TESTS);
        }

        randombytes(a, p.n * sizeof(uint8_t));
        memcpy(b, a, p.n * sizeof(uint8_t));  // a and b are equal

        res = memcmp_jazz(a, b);

        assert((memcmp(a, b, p.n * sizeof(uint8_t)) == 0) ? (res == 0) : (res == -1));
        assert(res == 0);
    }

    // a and b are not equal
    for (int i = 0; i < TESTS; i++) {
        if (debug) {
            printf("[memcmp 3] Test %d/%d\n", i + 1, TESTS);
        }

        do {
            randombytes(a, p.n * sizeof(uint8_t));
            randombytes(b, p.n * sizeof(uint8_t));
        } while (memcmp(a, b, p.n * sizeof(uint8_t) == 0));  // make sure a and b are not equal

        res = memcmp_jazz(a, b);

        assert((memcmp(a, b, p.n * sizeof(uint8_t)) == 0) ? (res == 0) : (res == -1));
        assert(res == -1);
    }
}

int main(void) {
    test_memset_zero_u8();
    test_memset_u8_ptr();
    test_memcmp();
    puts("MEM-* : OK");
    return 0;
}
