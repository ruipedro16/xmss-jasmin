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

#ifndef IMPL
#error IMPL not defined
#endif

#ifndef TESTS
#define TESTS 1000
#endif

#ifndef MAX_MSG_LEN
#define MAX_MSG_LEN 1024
#endif

#define MIN(a, b) ((a) < (b) ? (a) : (b))

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

extern int xmss_keypair_jazz(uint8_t *pk, uint8_t *sk);
extern int xmssmt_keypair_jazz(uint8_t *pk, uint8_t *sk);

extern int xmss_sign_jazz(uint8_t *sk, uint8_t *sm, size_t *smlen, const uint8_t *m, size_t mlen);
extern int xmssmt_sign_jazz(uint8_t *sk, uint8_t *sm, size_t *smlen, const uint8_t *m, size_t mlen);

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

static int starts_with(const char *str, const char *prefix) { return strncmp(str, prefix, strlen(prefix)) == 0; }

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

void test_randombytes() {
    // Test that the randombytes and randombytes1 streams are equal

#define BUF_SIZE 1024

    uint8_t x0[BUF_SIZE] = {0};
    uint8_t x1[BUF_SIZE] = {0};

    resetrandombytes();
    resetrandombytes1();

    for (int i = 0; i < TESTS; i++) {
        randombytes(x0, BUF_SIZE);
        randombytes1(x1, BUF_SIZE);

        assert(memcmp(x0, x1, BUF_SIZE) == 0);
    }

#undef BUF_SIZE

    puts("randombytes == randombytes1: OK");
}

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

void test_xmss_keypair(void) {
    // The C impl calls randombytes and the Jasmin impl calls randombytes1
    // We assume that both randombytes and randombytes1 output the same bytes (this test is only run
    // after the test that checks if randombytes == randombytes1)

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

    uint8_t pk_ref[XMSS_OID_LEN + p.pk_bytes];
    uint8_t sk_ref[XMSS_OID_LEN + p.sk_bytes];
    uint8_t pk_jasmin[XMSS_OID_LEN + p.pk_bytes];
    uint8_t sk_jasmin[XMSS_OID_LEN + p.sk_bytes];
    int res_jasmin, res_ref;

    for (int i = 0; i < TESTS; i++) {
        if (debug) {
            printf("[xmss keypair] Test %d/%d\n", i + 1, 100);
        }

        res_jasmin = xmss_keypair_jazz(pk_jasmin, sk_jasmin);
        res_ref = xmss_keypair(pk_ref, sk_ref, oid);

        assert(res_jasmin == res_ref);

        assert(memcmp(pk_ref, pk_jasmin, sizeof(uint32_t)) == 0);  // Compare the OID on the pk
        assert(memcmp(sk_ref, sk_jasmin, sizeof(uint32_t)) == 0);  // Compare the OID on the sk

        assert(memcmp(pk_ref, pk_jasmin, XMSS_OID_LEN + p.pk_bytes) == 0);  // Compare the whole key
        assert(memcmp(sk_ref, sk_jasmin, XMSS_OID_LEN + p.sk_bytes) == 0);  // Compare the whole key
    }
}

void test_xmssmt_keypair(void) {
    // The C impl calls randombytes and the Jasmin impl calls randombytes1
    // We assume that both randombytes and randombytes1 output the same bytes (this test is only run
    // after the test that checks if randombytes == randombytes1)

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

    uint8_t pk_ref[XMSS_OID_LEN + p.pk_bytes];
    uint8_t sk_ref[XMSS_OID_LEN + p.sk_bytes];
    uint8_t pk_jasmin[XMSS_OID_LEN + p.pk_bytes];
    uint8_t sk_jasmin[XMSS_OID_LEN + p.sk_bytes];
    int res_jasmin, res_ref;

    for (int i = 0; i < TESTS; i++) {
        if (debug) {
            printf("[xmss keypair] Test %d/%d\n", i + 1, 100);
        }

        res_jasmin = xmss_keypair_jazz(pk_jasmin, sk_jasmin);
        res_ref = xmss_keypair(pk_ref, sk_ref, oid);

        assert(res_jasmin == res_ref);

        assert(memcmp(pk_ref, pk_jasmin, sizeof(uint32_t)) == 0);  // Compare the OID on the pk
        assert(memcmp(sk_ref, sk_jasmin, sizeof(uint32_t)) == 0);  // Compare the OID on the sk

        assert(memcmp(pk_ref, pk_jasmin, XMSS_OID_LEN + p.pk_bytes) == 0);  // Compare the whole key
        assert(memcmp(sk_ref, sk_jasmin, XMSS_OID_LEN + p.sk_bytes) == 0);  // Compare the whole key
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

void test_xmss_sign(void) {
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

    uint8_t m[MAX_MSG_LEN];
    uint8_t pk[XMSS_OID_LEN + p.pk_bytes];
    uint8_t sk[XMSS_OID_LEN + p.sk_bytes];
    uint8_t sk0[XMSS_OID_LEN + p.sk_bytes];
    uint8_t sm_ref[p.sig_bytes + MAX_MSG_LEN];
    uint8_t sm_jasmin[p.sig_bytes + MAX_MSG_LEN];
    int res_ref, res_jasmin;
    size_t smlen_ref, smlen_jasmin;

    for (int i = 0; i < TESTS; i++) {
        for (size_t mlen = 1; mlen <= MAX_MSG_LEN; mlen++) {
            if (debug) {
                printf("[xmss sign] Test %d/%d (msg len = %ld/%d)\n", i + 1, TESTS, mlen, MAX_MSG_LEN);
            }

            // First we need to generate a keypair
            xmss_keypair(pk, sk, oid);

            memcpy(sk0, sk, XMSS_OID_LEN + p.sk_bytes);  // Because the sk is updated after signing

            res_ref = xmss_sign(sk, sm_ref, (unsigned long long *)&smlen_ref, m, mlen);
            res_jasmin = xmss_sign_jazz(sk0, sm_jasmin, &smlen_jasmin, m, mlen);

            assert(res_ref == res_jasmin);
            assert(memcmp(sk, sk0, XMSS_OID_LEN + p.sk_bytes) == 0);
            assert(smlen_jasmin == smlen_ref);
            assert(memcmp(sm_ref, sm_jasmin, p.sig_bytes + mlen) == 0);
        }
    }
}

void test_xmssmt_sign(void) {
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

    uint8_t m[MAX_MSG_LEN];
    uint8_t pk[XMSS_OID_LEN + p.pk_bytes];
    uint8_t sk[XMSS_OID_LEN + p.sk_bytes];
    uint8_t sk0[XMSS_OID_LEN + p.sk_bytes];
    uint8_t sm_ref[p.sig_bytes + MAX_MSG_LEN];
    uint8_t sm_jasmin[p.sig_bytes + MAX_MSG_LEN];
    int res_ref, res_jasmin;
    size_t smlen_ref, smlen_jasmin;

    for (int i = 0; i < TESTS; i++) {
        for (size_t mlen = 1; mlen <= MAX_MSG_LEN; mlen++) {
            if (debug) {
                printf("[xmssmt sign] Test %d/%d (msg len = %ld/%d)\n", i + 1, TESTS, mlen, MAX_MSG_LEN);
            }

            // First we need to generate a keypair
            xmssmt_keypair(pk, sk, oid);

            memcpy(sk0, sk, XMSS_OID_LEN + p.sk_bytes);  // Because the sk is updated after signing

            res_ref = xmssmt_sign(sk, sm_ref, (unsigned long long *)&smlen_ref, m, mlen);
            res_jasmin = xmssmt_sign_jazz(sk0, sm_jasmin, &smlen_jasmin, m, mlen);

            assert(res_ref == res_jasmin);
            assert(memcmp(sk, sk0, XMSS_OID_LEN + p.sk_bytes) == 0);
            assert(smlen_jasmin == smlen_ref);
            assert(memcmp(sm_ref, sm_jasmin, p.sig_bytes + mlen) == 0);
        }
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

void test_xmss_sk_reuse() {
    // This test checks that the signing functions returns -2 after signing 2^h messages

    // TODO:
}

void test_xmssmt_sk_reuse() {
    // This test checks that the signing functions returns -2 after signing 2^h messages

    // TODO:
}

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

int main(void) {

    test_randombytes();

    if (starts_with(xstr(IMPL), "XMSSMT")) {
        // test XMSSMT Variant
        test_xmssmt_keypair();
        test_xmssmt_sign();
    } else {
        // test XMSS Variant
        // test_xmss_keypair();
        test_xmss_sign();
    }

    return 0;
}