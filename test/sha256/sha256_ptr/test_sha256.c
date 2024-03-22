#include <assert.h>
#include <inttypes.h>
#include <openssl/sha.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "randombytes.h"

#ifndef TESTS
#define TESTS 100
#endif

#ifndef MAX_INLEN
#define MAX_INLEN 2048
#endif

extern void sha256_jazz(uint8_t *, const uint8_t *, size_t);

int main(void) {
    bool debug = true;

    uint8_t in[MAX_INLEN];
    uint8_t out_ref[SHA256_DIGEST_LENGTH], out_jazz[SHA256_DIGEST_LENGTH];  // SHA256_DIGEST_LENGTH = 32

    for (int i = 0; i < TESTS; i++) {
        for (size_t inlen = 0; inlen < MAX_INLEN; inlen++) {
            if (debug) {
                printf("[sha256_ptr]: Test %d/%d (INLEN=%ld)\n", i, TESTS, inlen);
            }

            sha256_jazz(out_jazz, in, inlen);
            SHA256((unsigned char *)in, inlen, (unsigned char *)out_ref);

            assert(memcmp(out_jazz, out_jazz, SHA256_DIGEST_LENGTH) == 0);
        }
    }

    printf("SHA256 OK\n");
    return 0;
}