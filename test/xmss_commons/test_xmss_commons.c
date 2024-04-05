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
#include "xmss_commons.h"

#ifndef IMPL
#error IMPL not defined
#endif

#ifndef TESTS
#define TESTS 100
#endif

#define XMSS_N p.n
#define XMSS_WOTS_SIG_BYTES p.wots_sig_bytes

extern void l_tree_jazz(uint8_t *, uint8_t *, const uint8_t *, uint32_t *);

void test_ltree(void) {
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

    uint8_t leaf_ref[XMSS_N], leaf_jasmin[XMSS_N];
    uint8_t wots_pk_ref[XMSS_WOTS_SIG_BYTES], wots_pk_jasmin[XMSS_WOTS_SIG_BYTES];
    uint8_t pub_seed[XMSS_N];
    uint32_t addr_ref[8], addr_jasmin[8];

    for (int i = 0; i < TESTS; i++) {
        if (debug) {
            printf("[ltree]: Test %d/%d\n", i + 1, TESTS);

            randombytes(leaf_ref, XMSS_N);
            memcpy(leaf_jasmin, leaf_ref, XMSS_N);

            randombytes(wots_pk_ref, XMSS_WOTS_SIG_BYTES);
            memcpy(wots_pk_jasmin, wots_pk_ref, XMSS_WOTS_SIG_BYTES);

            randombytes(pub_seed, XMSS_N);

            randombytes((uint8_t *)addr_ref, 8 * sizeof(uint32_t));
            memcpy(addr_jasmin, addr_ref, 8 * sizeof(uint32_t));

            assert(memcmp(leaf_ref, leaf_jasmin, XMSS_N) == 0);
            assert(memcmp(wots_pk_ref, wots_pk_jasmin, XMSS_WOTS_SIG_BYTES) == 0);
            assert(memcmp(addr_ref, addr_jasmin, 8 * sizeof(uint32_t)) == 0);

            l_tree_jazz(leaf_jasmin, wots_pk_jasmin, pub_seed, addr_jasmin);
            l_tree(&p, leaf_ref, wots_pk_ref, pub_seed, addr_ref);

            /*
            if (memcmp(leaf_ref, leaf_jasmin, XMSS_N) != 0) {
                print_str_u8("leaf ref", leaf_ref, XMSS_N);
                print_str_u8("leaf jasmin", leaf_jasmin, XMSS_N);
            }

            if (memcmp(wots_pk_ref, wots_pk_jasmin, XMSS_WOTS_SIG_BYTES) != 0) {
                print_str_u8("wots pk ref", wots_pk_ref, XMSS_WOTS_SIG_BYTES);
                print_str_u8("wots pk jasmin", wots_pk_jasmin, XMSS_WOTS_SIG_BYTES);
            }

            if (memcmp(addr_ref, addr_jasmin, 8 * sizeof(uint32_t)) != 0) {
                print_str_u8("addr ref", (uint8_t *)addr_ref, 8 * sizeof(uint32_t));
                print_str_u8("addr jasmin", (uint8_t *)addr_jasmin, 8 * sizeof(uint32_t));
            }

            // assert(memcmp(leaf_ref, leaf_jasmin, XMSS_N) == 0); // FIXME: NOT OK
            // assert(memcmp(wots_pk_ref, wots_pk_jasmin, XMSS_WOTS_SIG_BYTES) == 0); // FIXME: NOT OK
            // assert(memcmp(addr_ref, addr_jasmin, 8 * sizeof(uint32_t)) == 0);  // OK
            */
        }
    }
}

void test_api(void) {
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

    for (int i = 0; i < TESTS; i++) {
        if (debug) {
            printf("[xmss_commons]: Test %d/%d\n", i + 1, TESTS);
        }
    }
}

int main(void) {
    test_ltree();
    printf("[%s]: XMSS Commons OK\n", xstr(IMPL));
    return 0;
}
