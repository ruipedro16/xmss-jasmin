#include <assert.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "fips202.h"
#include "hash.h"
#include "macros.h"
#include "params.h"
#include "print.h"
#include "randombytes.h"

#ifndef IMPL
#error IMPL not defined
#endif

#ifndef INLEN
#error INLEN not defined
#endif

#ifndef MAX_INLEN
#define MAX_INLEN 128
#endif

#ifndef TESTS
#define TESTS 1000
#endif

#define core_hash_jazz NAMESPACE1(core_hash, INLEN)
extern void core_hash_jazz(uint8_t *, const uint8_t *);
extern void core_hash_in_ptr(uint8_t *, const uint8_t *, size_t);

void test_core_hash(void) {
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

    uint8_t out_ref[64], out_jazz[64];
    uint8_t in[INLEN];

    for (int i = 0; i < TESTS; i++) {
        if (debug) {
            printf("[core_hash (INLEN=%d)]: Test %d/%d\n", INLEN, i + 1, TESTS);

            randombytes(in, INLEN);
            core_hash_jazz(out_jazz, in);
            core_hash(&p, out_ref, in, INLEN);

            assert(memcmp(out_ref, out_jazz, 64) == 0);
        }
    }
}

void test_core_hash_in_ptr(void) {
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

    uint8_t out_ref[64], out_jazz[64];
    uint8_t in[MAX_INLEN];

    for (int i = 0; i < TESTS; i++) {
        for (size_t inlen = 1; inlen <= MAX_INLEN; inlen++) {
            if (debug) {
                printf("[core_hash_in_ptr (INLEN=%d)]: Test %d/%d\n", INLEN, i + 1, TESTS);
            }

            randombytes(in, inlen);
            core_hash_in_ptr(out_jazz, in, inlen);
            core_hash(&p, out_ref, in, inlen);

            assert(memcmp(out_ref, out_jazz, 64) == 0);
        }
    }
}

int main(void) {
    test_core_hash();
    test_core_hash_in_ptr();
    printf("Core Hash OK\n");
    return 0;
}