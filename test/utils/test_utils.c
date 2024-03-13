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

#ifndef OUTLEN
#error OUTLEN not defined
#endif

#ifndef INLEN
#error INLEN not defined
#endif

#ifndef LEN
#error LEN not defined
#endif

#define ull_to_bytes_jazz NAMESPACE1(ull_to_bytes_jazz, OUTLEN)
extern void ull_to_bytes_jazz(uint8_t *, uint64_t);

#define bytes_to_ull_jazz NAMESPACE1(bytes_to_ull_jazz, INLEN)
extern uint64_t bytes_to_ull_jazz(const uint8_t *);

extern void zero_address_jazz(uint32_t *);

#define memset_jazz NAMESPACE1(memset_jazz, LEN)
extern void memset_jazz(uint8_t *, uint8_t);

void test_ull_to_bytes(void) {
    uint64_t in;
    uint8_t out_ref[OUTLEN], out_jazz[OUTLEN];

    for (int i = 0; i < TESTS; i++) {
        randombytes((uint8_t *)&in, sizeof(uint64_t));
        randombytes((uint8_t *)out_ref, OUTLEN);
        memcpy(out_jazz, out_ref, OUTLEN);

        ull_to_bytes_jazz(out_jazz, in);
        ull_to_bytes(out_ref, OUTLEN, in);

        assert(memcmp(out_ref, out_jazz, OUTLEN) == 0);
    }
}

void test_bytes_to_ull(void) {
    uint64_t out_ref, out_jazz;
    uint8_t in[INLEN];
    for (int i = 0; i < TESTS; i++) {
        randombytes(in, INLEN);

        out_ref = bytes_to_ull(in, INLEN);
        out_jazz = bytes_to_ull_jazz(in);

        assert(out_ref == out_jazz);
    }
}

void test_zero_address(void) {
    uint32_t addr_ref[8], addr_jazz[8];

    for (int i = 0; i < TESTS; i++) {
        randombytes((uint8_t *)addr_ref, 8 * sizeof(uint32_t));
        memcpy(addr_jazz, addr_ref, 8 * sizeof(uint16_t));

        zero_address_jazz(addr_jazz);
        memset(addr_ref, 0, 8 * sizeof(uint32_t));

        if (memcmp(addr_ref, addr_jazz, 8 * sizeof(uint32_t)) != 0) {
            print_str_u8("Ref", (uint8_t *)addr_ref, 8 * sizeof(uint32_t));
            print_str_u8("Jasmin", (uint8_t *)addr_jazz, 8 * sizeof(uint32_t));
        }

        assert(memcmp(addr_ref, addr_jazz, 8 * sizeof(uint32_t)) == 0);
    }
}

void test_memset(void) {
    uint8_t val;
    uint8_t buf_ref[LEN], buf_jazz[LEN];
    for (int i = 0; i < TESTS; i++) {
        randombytes(&val, sizeof(uint8_t));

        memset_jazz(buf_jazz, val);
        memset(buf_ref, val, LEN * sizeof(uint8_t));

        assert(memcmp(buf_ref, buf_jazz, LEN * sizeof(uint8_t)) == 0);
    }
}

int main(void) {
    test_ull_to_bytes();
    test_bytes_to_ull();
    test_zero_address();
    test_memset();
    printf("Utils[INLEN=%s, OUTLEN=%s, LEN=%s]: OK\n", xstr(INLEN), xstr(OUTLEN), xstr(LEN));
}
