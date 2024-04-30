#include <assert.h>
#include <inttypes.h>
#include <openssl/sha.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "macros.h"
#include "print.h"
#include "randombytes.h"

#ifndef INLEN
#error INLEN not defined
#endif

#ifndef TESTS
#define TESTS 1000
#endif

#define sha256_jazz NAMESPACE1(sha256_array, INLEN)
extern void sha256_jazz(uint8_t *, const uint8_t *);

int main(void) {
    bool debug = true;

    uint8_t in[INLEN] = {0};
    uint8_t out_ref[SHA256_DIGEST_LENGTH] = {0};
    uint8_t out_jazz[SHA256_DIGEST_LENGTH] = {0};  // SHA256_DIGEST_LENGTH = 32

    for (int i = 0; i < TESTS; i++) {
        if (debug) {
            printf("[sha256_ptr]: Test %d/%d (INLEN=%d)\n", i, TESTS, INLEN);
        }

        randombytes(in, INLEN);

        sha256_jazz(out_jazz, in);
        SHA256((unsigned char *)in, INLEN, (unsigned char *)out_ref);

        // if (debug) {
        //     print_str_u8("sha256 ref", out_ref, SHA256_DIGEST_LENGTH);
        //     print_str_u8("sha256 jasmin", out_jazz, SHA256_DIGEST_LENGTH);
        // }

        assert(memcmp(out_ref, out_jazz, SHA256_DIGEST_LENGTH) == 0);
    }

    printf("SHA256 OK (INLEN=%d)\n", INLEN);
    return 0;
}
