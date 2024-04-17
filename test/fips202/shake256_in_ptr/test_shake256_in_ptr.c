#include <assert.h>
#include <inttypes.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>

#include "fips202.h"
#include "macros.h"
#include "print.h"
#include "randombytes.h"

#ifndef OUTLEN
#error OUTLEN not defined
#endif

#ifndef MAX_INLEN
#define MAX_INLEN 1024
#endif

#ifndef TESTS
#define TESTS 1000
#endif

#define shake256_jazz NAMESPACE1(shake256, OUTLEN)

extern void shake256_jazz(uint8_t *out, const uint8_t *in, size_t inlen);

int main(void) {
    bool debug = true;

    uint8_t out_jazz[OUTLEN], out_ref[OUTLEN];
    uint8_t in[MAX_INLEN];

    for (int t = 0; t < TESTS; t++) {
        for (size_t inlen = 1; inlen < MAX_INLEN; inlen++) {
            if (debug) {
                printf("[Test %d/%d]: shake256_in_ptr { outlen: %d ; inlen: %ld}\n", t+1, TESTS, OUTLEN, inlen);
            }

            randombytes(in, inlen);

            shake256_jazz(out_jazz, in, inlen);
            shake256(out_ref, OUTLEN, in, inlen);

            assert(memcmp(out_jazz, out_ref, OUTLEN) == 0);
        }
    }

    printf("PASS: fips202 in_ptr = { outlen: %d }\n", OUTLEN);
}
