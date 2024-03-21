#include <assert.h>
#include <inttypes.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "fips202.h"
#include "macros.h"
#include "notrandombytes.c"
#include "print.c"

#ifndef TESTS
#define TESTS 1000
#endif

#ifndef MAX_INLEN
#define MAX_INLEN 2048
#endif

#ifndef MAX_OUTLEN
#define MAX_OUTLEN 2048
#endif

extern void shake256_ptr_jazz(uint8_t *out, size_t outlen, const uint8_t *in, size_t inlen);

int main(void) {
    uint8_t *in;
    uint8_t *out_ref;
    uint8_t *out_jazz;

    for (int i = 0; i < TESTS; i++) {
        for (size_t inlen = 0; inlen < MAX_INLEN; inlen++) {
            for (size_t outlen = 0; outlen < MAX_OUTLEN; outlen++) {
                printf("[Test %d/%d]: INLEN: %ld OUTLEN: %ld\n", i, TESTS, inlen, outlen);
                in = malloc(inlen);
                out_ref = malloc(outlen);
                out_jazz = malloc(outlen);

                randombytes(in, inlen);

                shake256_ptr_jazz(out_jazz, outlen, in, inlen);
                shake256(out_ref, outlen, in, inlen);

                assert(memcmp(out_jazz, out_ref, outlen) == 0);

                free(in);
                free(out_ref);
                free(out_jazz);
            }
        }
    }

    printf("Pass: shake256_ptr\n");

    return 0;
}
