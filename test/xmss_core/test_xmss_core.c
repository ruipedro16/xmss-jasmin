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
#include "xmss_core.h"

#ifndef IMPL
#error IMPL not defined
#endif

#ifndef TESTS
#define TESTS 100
#endif

extern void treehash_jazz(uint8_t *auth_path, uint8_t *root, const uint8_t *sk_seed, const uint8_t *pub_seed,
                                uint32_t leaf_idx, const uint32_t subtree_addr[8]);

extern int xmssmt_core_seed_keypair_jazz(uint8_t *pk, uint8_t *sk, const uint8_t *seed);

static int starts_with(const char *str, const char *prefix) { return strncmp(str, prefix, strlen(prefix)) == 0; }

void test_keypair_seed(void) {
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

    uint8_t pk_ref[p.pk_bytes];
    uint8_t sk_ref[p.sk_bytes];

    uint8_t pk_jasmin[p.pk_bytes];
    uint8_t sk_jasmin[p.sk_bytes];

    uint8_t seed[3 * p.n];

    memset(seed, 3 * p.n, 72);

    int res_ref, res_jasmin;

    for (int i = 0; i < 100; i++) {
        if (debug) {
            printf("[KEY PAIR SEED] Test %d/%d\n", i + 1, 100);
        }

        memset(pk_ref, 0, p.pk_bytes);
        memset(sk_ref, 0, p.sk_bytes);

        memset(pk_jasmin, 0, p.pk_bytes);
        memset(sk_jasmin, 0, p.sk_bytes);

        res_jasmin = xmssmt_core_seed_keypair_jazz(pk_jasmin, sk_jasmin, seed);
        res_ref = xmssmt_core_seed_keypair(&p, pk_ref, sk_ref, seed);

        assert(res_jasmin == 0);
        assert(res_ref == 0);

        assert(memcmp(pk_ref, pk_jasmin, p.pk_bytes) == 0);
        assert(memcmp(sk_ref, sk_jasmin, p.sk_bytes) == 0);
    }
}

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
    // [X] treehash array
    // [ ] xmssmt_core_seed_keypair

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
            printf("[XMSS] Test %d/%d\n", i + 1, 100);
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

    puts("[XMSS] OK");
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

    // C functions replaced by corresponding Jasmin functions:
    // TODO:

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
            printf("[XMSS] Test %d/%d\n", i + 1, 100);
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

    puts("[XMSS] OK");
}

int main(void) {
    // test_keypair_seed(); // OK
    starts_with(xstr(IMPL), "XMSSMT") ? test_xmssmt() : test_xmss();
    printf("[%s]: XMSS Core OK\n", xstr(IMPL));
    return 0;
}