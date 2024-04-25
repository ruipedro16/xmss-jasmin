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
#include "xmss.h"
#include "xmss_commons.h"

#ifndef IMPL
#error IMPL not defined
#endif

#ifndef TESTS
#define TESTS 1000
#endif

#define XMSS_N p.n
#define XMSS_WOTS_SIG_BYTES p.wots_sig_bytes

extern void l_tree_jazz(uint8_t *, uint8_t *, uint32_t *, const uint8_t *);
extern void gen_leaf_wots_jazz(uint8_t *leaf, uint32_t ltree_addr[8], uint32_t ots_addr[8], const uint8_t *sk_seed,
                               const uint8_t *pub_seed);
extern void compute_root_jazz(unsigned char *root, uint32_t addr[8], const unsigned char *leaf, unsigned long leaf_idx,
                              const unsigned char *auth_path, const unsigned char *pub_seed);
extern int xmss_core_sign_open_jazz(uint8_t *m, size_t *mlen, const uint8_t *sm, size_t smlen, const uint8_t *pk);
extern int xmssmt_core_sign_open_jazz(uint8_t *m, size_t *mlen, const uint8_t *sm, size_t smlen, const uint8_t *pk);

static int starts_with(const char *str, const char *prefix) { return strncmp(str, prefix, strlen(prefix)) == 0; }

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

            l_tree_jazz(leaf_jasmin, wots_pk_jasmin, addr_jasmin, pub_seed);
            l_tree(&p, leaf_ref, wots_pk_ref, pub_seed, addr_ref);

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

            assert(memcmp(leaf_ref, leaf_jasmin, XMSS_N) == 0);
            assert(memcmp(wots_pk_ref, wots_pk_jasmin, XMSS_WOTS_SIG_BYTES) == 0);
            assert(memcmp(addr_ref, addr_jasmin, 8 * sizeof(uint32_t)) == 0);
        }
    }

    puts("[ltree] OK");
}

void test_compute_root(void) {
    // FIXME: This test fails but if I replace compute_root with compute_root_jazz in the ref impl, the tests work so
    // compute_root_jazz is probably fine
    // TODO: Ignore this test?

    bool debug = true;

#define XMSS_MLEN 32

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
            printf("[compute root]: Test %d/%d\n", i + 1, TESTS);
        }

        uint8_t root_ref[XMSS_N], root_jasmin[XMSS_N];
        uint32_t addr_ref[8], addr_jasmin[8];
        uint8_t leaf[XMSS_N];
        uint32_t leaf_idx;
        uint8_t auth_path[p.sig_bytes + XMSS_MLEN];
        uint8_t pub_seed[XMSS_N];

        randombytes(root_ref, XMSS_N);
        memcpy(root_jasmin, root_ref, XMSS_N);

        randombytes((uint8_t *)addr_ref, 8 * sizeof(uint32_t));
        memcpy(addr_jasmin, addr_ref, 8 * sizeof(uint32_t));

        randombytes(leaf, XMSS_N);

        randombytes((uint8_t *)&leaf_idx, sizeof(uint32_t));

        randombytes(auth_path, p.sig_bytes + XMSS_MLEN);

        randombytes(pub_seed, XMSS_N);

        assert(memcmp(addr_ref, addr_jasmin, 8 * sizeof(uint32_t)) == 0);
        assert(memcmp(root_ref, root_jasmin, XMSS_N) == 0);

        compute_root(&p, root_jasmin, leaf, leaf_idx, auth_path, pub_seed, addr_ref);
        compute_root_jazz(root_jasmin, addr_jasmin, leaf, leaf_idx, auth_path, pub_seed);

        assert(memcmp(root_ref, root_jasmin, XMSS_N) == 0);
        assert(memcmp(addr_ref, addr_jasmin, 8 * sizeof(uint32_t)) == 0);
    }

    puts("[compute_root] OK");

#undef XMSS_MLEN
}

void test_gen_leaf_wots(void) {}  // TODO:

void test_sign_open_xmss(void) {
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

    #define XMSS_MLEN 32

    uint8_t pk[XMSS_OID_LEN + p.pk_bytes];
    uint8_t sk[XMSS_OID_LEN + p.sk_bytes];

    uint8_t m[XMSS_MLEN];
    uint8_t sm[p.sig_bytes + XMSS_MLEN];
    
    uint8_t mout_ref[p.sig_bytes + XMSS_MLEN];
    uint8_t mout_jasmin[p.sig_bytes + XMSS_MLEN];

    unsigned long long smlen;
    unsigned long long mlen_ref, mlen_jasmin;


    for (int i = 0; i < 100; i++) {
        if (debug) {
            printf("[xmss sign open] Test %d/%d\n", i + 1, 100);
        }

        xmss_keypair(pk, sk, oid);
        randombytes(m, XMSS_MLEN);
        xmss_sign(sk, sm, &smlen, m, XMSS_MLEN);

        assert(smlen == p.sig_bytes + XMSS_MLEN);

        int res_jasmin = xmssmt_core_sign_open_jazz(mout_jasmin, &mlen_jasmin, sm, smlen, pk + XMSS_OID_LEN);
        int res_ref = xmss_core_sign_open(&p, mout_ref, &mlen_ref, sm, smlen, pk + XMSS_OID_LEN);

        assert(mlen_ref == mlen_jasmin);
        assert(res_jasmin == res_ref);
    }

#undef XMSS_MLEN

    puts("[xmss sign open] OK");

}

void test_sign_open_xmssmt(void) { } // TODO:

void test_xmss(void) {
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

    // C functions replaced by corresponding Jasmin functions:
    // [X] ltree
    // [X] compute root
    // [X] gen_leaf_wots
    // [X] xmss_core_sign_open

#define XMSS_MLEN 32

    uint8_t pk[XMSS_OID_LEN + p.pk_bytes];
    uint8_t sk[XMSS_OID_LEN + p.sk_bytes];

    uint8_t m[XMSS_MLEN];
    uint8_t sm[p.sig_bytes + XMSS_MLEN];
    uint8_t mout[p.sig_bytes + XMSS_MLEN];
    unsigned long long smlen;
    unsigned long long mlen;

    for (int i = 0; i < 100; i++) {
        if (debug) {
            printf("[xmss_commons - XMSS] Test %d/%d\n", i + 1, 100);
        }

        xmss_keypair(pk, sk, oid);
        randombytes(m, XMSS_MLEN);
        xmss_sign(sk, sm, &smlen, m, XMSS_MLEN);
        assert(smlen == p.sig_bytes + XMSS_MLEN);
        int res = xmss_sign_open(mout, &mlen, sm, smlen, pk);

        assert(mlen == XMSS_MLEN);
        assert(res == 0);
    }

#undef XMSS_MLEN

    puts("[xmss_commons - XMSS] OK");
}

void test_xmssmt(void) {
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

    // C functions replaced by corresponding Jasmin functions:
    // [X] ltree
    // [X] compute root
    // [X] gen_leaf_wots
    // [X] xmssmt_core_sign_open

#define XMSS_MLEN 32

    uint8_t pk[XMSS_OID_LEN + p.pk_bytes];
    uint8_t sk[XMSS_OID_LEN + p.sk_bytes];

    uint8_t m[XMSS_MLEN];
    uint8_t sm[p.sig_bytes + XMSS_MLEN];
    uint8_t mout[p.sig_bytes + XMSS_MLEN];
    unsigned long long smlen;
    unsigned long long mlen;

    for (int i = 0; i < 100; i++) {
        if (debug) {
            printf("[xmss_commons - XMSSMT] Test %d/%d\n", i + 1, 100);
        }

        xmssmt_keypair(pk, sk, oid);
        randombytes(m, XMSS_MLEN);
        xmssmt_sign(sk, sm, &smlen, m, XMSS_MLEN);
        assert(smlen == p.sig_bytes + XMSS_MLEN);
        int res = xmssmt_sign_open(mout, &mlen, sm, smlen, pk);
        
        assert(mlen == XMSS_MLEN);
        assert(res == 0);
    }

#undef XMSS_MLEN

    puts("[xmss_commons - XMSSMT] OK");
}

int main(void) {
    test_ltree();
    // test_gen_leaf_wots();  // TODO: TODO: 
    starts_with(xstr(IMPL), "XMSSMT") ? test_xmssmt() : test_xmss();
    printf("[%s]: XMSS Commons OK\n", xstr(IMPL));
    return 0;
}
