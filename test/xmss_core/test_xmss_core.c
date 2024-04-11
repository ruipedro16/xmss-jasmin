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

    for (int i = 0; i < TESTS; i++) {
        if (debug) {
            printf("[xmss_core]: Test %d/%d\n", i + 1, TESTS);
        }
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
    unsigned long long mlen = XMSS_MLEN;

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
    unsigned long long mlen = XMSS_MLEN;

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
    test_xmss();
    test_xmssmt();
    printf("[%s]: XMSS Core OK\n", xstr(IMPL));
    return 0;
}