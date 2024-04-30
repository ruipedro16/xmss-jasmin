#include <assert.h>
#include <inttypes.h>
#include <openssl/sha.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "print.h"
#include "randombytes.h"

#ifndef TESTS
#define TESTS 1000
#endif

#ifndef MAX_INLEN
#define MAX_INLEN 2048
#endif

extern void sha256_in_ptr_jazz(uint8_t *, const uint8_t *, size_t);

int main(void) {
    bool debug = true;

    uint8_t in[MAX_INLEN];
    uint8_t out_ref[SHA256_DIGEST_LENGTH] = {0};
    uint8_t out_jazz[SHA256_DIGEST_LENGTH] = {0};  // SHA256_DIGEST_LENGTH = 32

    for (int i = 0; i < TESTS; i++) {
        for (size_t inlen = 0; inlen < MAX_INLEN; inlen++) {
            if (debug) {
                printf("[sha256_in_ptr]: Test %d/%d (INLEN=%ld)\n", i, TESTS, inlen);
            }

            randombytes(in, inlen);

            sha256_in_ptr_jazz(out_jazz, in, inlen);
            SHA256((unsigned char *)in, inlen, (unsigned char *)out_ref);

            // if (debug) {
            //     print_str_u8("sha256 ref", out_ref, SHA256_DIGEST_LENGTH);
            //     print_str_u8("sha256 jasmin", out_jazz, SHA256_DIGEST_LENGTH);
            // }

            assert(memcmp(out_jazz, out_jazz, SHA256_DIGEST_LENGTH) == 0);
        }
    }

    printf("SHA256 OK\n");
    return 0;
}
