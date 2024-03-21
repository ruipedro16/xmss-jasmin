#include <assert.h>
#include <inttypes.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "fips202.h"
#include "macros.h"
#include "print.h"
#include "randombytes.h"

#ifndef OUTLEN
#error OUTLEN not defined
#endif

#ifndef INLEN
#error INLEN not defined
#endif

#ifndef TESTS
#define TESTS 1000
#endif

#define shake256_jazz NAMESPACE2(shake256, OUTLEN, INLEN)

extern void shake256_jazz(uint8_t *out, const uint8_t *in);

int main() {
    uint8_t out_jazz[OUTLEN], out_ref[OUTLEN];
    uint8_t in[INLEN];

    for (int t = 0; t < TESTS; t++) {
        randombytes(in, INLEN);

        shake256_jazz(out_jazz, in);
        shake256(out_ref, OUTLEN, in, INLEN);

        assert(memcmp(out_jazz, out_ref, OUTLEN) == 0);
    }

    printf("PASS: fips202 array = { outlen: %d, inlen: %d }\n", OUTLEN, INLEN);
}
