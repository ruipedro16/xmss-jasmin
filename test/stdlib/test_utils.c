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

#ifndef MAX_LEN
#define MAX_LEN 1024
#endif

// bytes
extern uint64_t bytes_to_ull_jazz(const uint8_t *);

extern void memset_zero_u8_jazz(uint8_t *);

extern uint64_t bytes_to_ull_ptr_jazz(const uint8_t *, size_t);

// memcpy
#define memcpy_u8u8_jazz NAMESPACE2(memcpy_u8u8_jazz, INLEN, INLEN)  // TODO: FIXME: replace with outlen
extern void memcpy_u8u8_jazz(uint8_t *, size_t, const uint8_t *);

extern void memcpy_u8pu8p_jazz(uint8_t *, size_t, const uint8_t *, size_t, size_t);

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
    // TODO: Remove unnecessary template parameter
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

void test_memcpy_u8u8(void) {
#define _TESTS 100

    bool debug = true;

    uint8_t out[INLEN] = {0};
    uint8_t in[INLEN] = {0};
    size_t offset=0;

    for (int i = 0; i < _TESTS; i++) {
        // for (size_t offset = 0; offset <= OUTLEN - INLEN; offset++) {
            if (debug) {
                printf("[memcpy_u8u8] (INLEN=%s, OUTLEN=%s, offset=%d): Test %d/%d\n", xstr(INLEN), xstr(INLEN), 0,
                       i + 1, _TESTS);
            }

            randombytes(in, INLEN);
            memset(out, 0, INLEN);

            memcpy_u8u8_jazz(out, 0, in);

            if (memcmp(out, in, INLEN) != 0) {
                print_str_u8("in", in, INLEN);
                print_str_u8("out", out, INLEN);
            }

            assert(memcmp(out + offset, in, INLEN) == 0);
        }
    // }

    // TODO: Test with offset != 0

#undef _TESTS
}

void test_memcpy_u8pu8p(void) {
#define _TESTS 100

    bool debug = true;

    uint8_t in[MAX_LEN];
    uint8_t out_ref[MAX_LEN], out_jazz[MAX_LEN];
    size_t offset_out, offset_in;
    size_t len;

    for (int i = 0; i < _TESTS; i++) {
        for (size_t inlen = 1; inlen < MAX_LEN; inlen++) {
            for (size_t outlen = 1; outlen < MAX_LEN; outlen++) {
                randombytes(in, inlen);
                memset(out_ref, 0, outlen);
                memset(out_jazz, 0, outlen);

                offset_in = rand() % inlen;
                offset_out = rand() % outlen;
                len = rand() % (inlen - offset_in);

                // Adjust len to ensure it fits within the output length
                if (len > outlen - offset_out) {
                    len = outlen - offset_out;
                }

                // ensure we dont read out of bounds
                assert(offset_out + len <= outlen);
                assert(offset_in + len <= inlen);

                if (debug) {
                    printf(
                        "[memcpy_u8pu8p (INLEN=%ld;OUTLEN=%ld) : (offset_in=%ld;offset_out=%ld;len=%ld)]\tTest %d/%d\n",
                        inlen, outlen, offset_in, offset_out, len, i, _TESTS);
                }

                memcpy(out_ref + offset_out, in + offset_in, len);
                memcpy_u8pu8p_jazz(out_jazz, offset_out, in, offset_in, len);

                if (memcmp(out_ref, out_jazz, outlen) != 0) {
                    print_str_u8("in", in, inlen);
                    printf("\n\noffset_out = %ld ; offset_in = %ld, len = %ld\n\n", offset_out, offset_in, len);
                    print_str_u8("out ref", out_ref, outlen);
                    print_str_u8("out jazz", out_jazz, outlen);
                }

                assert(memcmp(out_ref, out_jazz, outlen) == 0);
            }
        }
    }

#undef _TESTS
}

int main(void) {
    // test_bytes_to_ull();
    test_bytes_to_ull_ptr();
    test_memcpy_u8u8();
    test_memcpy_u8pu8p();
    printf("Utils [INLEN=%d]: OK\n", INLEN);
    return 0;
}
