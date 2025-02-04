#include <assert.h>
#include <inttypes.h>
#include <math.h>
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
#define TESTS 10
#endif

#ifndef MAX_MSG_LEN
#define MAX_MSG_LEN 1024
#endif

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

extern int xmss_keypair_jazz(uint8_t *pk, uint8_t *sk);
extern int xmssmt_keypair_jazz(uint8_t *pk, uint8_t *sk);

extern int xmss_sign_jazz(uint8_t *sk, uint8_t *sm, size_t *smlen, const uint8_t *m, size_t mlen);
extern int xmssmt_sign_jazz(uint8_t *sk, uint8_t *sm, size_t *smlen, const uint8_t *m, size_t mlen);

extern int xmss_sign_open_jazz(uint8_t *m, size_t *mlen, const uint8_t *sm, size_t smlen, const uint8_t *pk);
extern int xmssmt_sign_open_jazz(uint8_t *m, size_t *mlen, const uint8_t *sm, size_t smlen, const uint8_t *pk);

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

static int starts_with(const char *str, const char *prefix) { return strncmp(str, prefix, strlen(prefix)) == 0; }

static void bitflip(uint8_t *x, size_t len) {
    // Flips one bit (chosen at random)
    size_t index;
    randombytes((uint8_t *)&index, sizeof(size_t));
    index = index % (len * 8);

    size_t byte_index = index / 8;
    size_t bit_index = index % 8;

    x[byte_index] ^= (1 << bit_index);
}

static size_t longestCommonPrefixSize(const uint8_t *array1, const uint8_t *array2, size_t length) {
    size_t prefixLength = 0;

    for (size_t i = 0; i < length; i++) {
        if (array1[i] == array2[i]) {
            prefixLength++;
        } else {
            return prefixLength;
        }
    }

    return prefixLength;
}

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
            printf("[xmss keypair] Test %d/%d\n", i + 1, TESTS);
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

    if (xmssmt_str_to_oid(&oid, xstr(IMPL)) == -1) {
        fprintf(stderr, "Failed to generate oid from impl name\n");
        exit(-1);
    }

    if (xmssmt_parse_oid(&p, oid) == -1) {
        fprintf(stderr, "Failed to generate params from oid\n");
        exit(-1);
    }

    /* Format sk: [OID || (32bit) idx || SK_SEED || SK_PRF || PUB_SEED || root] */
    /* Na SK, na verdade a root ta a seguir ao idx */
    /* Format pk: [OID || root || PUB_SEED] */
    uint8_t pk_ref[XMSS_OID_LEN + p.pk_bytes];
    uint8_t sk_ref[XMSS_OID_LEN + p.sk_bytes];
    uint8_t pk_jasmin[XMSS_OID_LEN + p.pk_bytes];
    uint8_t sk_jasmin[XMSS_OID_LEN + p.sk_bytes];
    int res_jasmin, res_ref;

    for (int i = 0; i < TESTS; i++) {
        if (debug) {
            printf("[xmssmt keypair] Test %d/%d\n", i + 1, TESTS);
        }

        res_ref = xmssmt_keypair(pk_ref, sk_ref, oid);

        if (debug && false) {
            puts("Ref finished");
        }

        res_jasmin = xmss_keypair_jazz(pk_jasmin, sk_jasmin); 

        assert(res_jasmin == res_ref);

        assert(memcmp(pk_ref, pk_jasmin, sizeof(uint32_t)) == 0);  // Compare the OID on the pk
        assert(memcmp(sk_ref, sk_jasmin, sizeof(uint32_t)) == 0);  // Compare the OID on the sk

        if (debug) {
            if (memcmp(pk_ref, pk_jasmin, XMSS_OID_LEN + p.pk_bytes) != 0) {
                printf("Longest match on the pk: %ld bytes\n",
                       longestCommonPrefixSize(pk_ref, pk_jasmin, XMSS_OID_LEN + p.pk_bytes));

                if (memcmp(pk_ref + XMSS_OID_LEN + p.n, pk_jasmin + XMSS_OID_LEN + p.n, p.n) == 0) {
                    puts("Pub seed matches on the PK");
                } else {
                    puts("Pub seed does not match on the PK");
                }
            }
        }

        assert(memcmp(sk_ref, sk_jasmin, XMSS_OID_LEN + p.sk_bytes) == 0);  // Compare the whole key
        assert(memcmp(pk_ref, pk_jasmin, XMSS_OID_LEN + p.pk_bytes) == 0);  // Compare the whole key
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
        size_t mlen = MAX_MSG_LEN;  
                                    

        memset(sm_ref, 0, p.sig_bytes + MAX_MSG_LEN);
        memset(sm_jasmin, 0, p.sig_bytes + MAX_MSG_LEN);

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

        if ((memcmp(sm_ref, sm_jasmin, p.sig_bytes + mlen) != 0) && true) {
            print_str_u8("reference", sm_ref, p.sig_bytes + mlen);
            print_str_u8("jasmin", sm_jasmin, p.sig_bytes + mlen);
        }

        assert(memcmp(sm_ref, sm_jasmin, p.sig_bytes + mlen) == 0);
    }
    // }
}

void test_xmssmt_sign(void) {
    bool debug = true;

    xmss_params p;
    uint32_t oid;

    if (xmssmt_str_to_oid(&oid, xstr(IMPL)) == -1) {
        fprintf(stderr, "Failed to generate oid from impl name\n");
        exit(-1);
    }

    if (xmssmt_parse_oid(&p, oid) == -1) {
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
        size_t mlen = MAX_MSG_LEN;
        // for (size_t mlen = 1; mlen <= MAX_MSG_LEN; mlen++) {
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
    // }
}

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

void test_xmss_sign_open(void) {
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
    uint8_t sm[p.sig_bytes + MAX_MSG_LEN];
    size_t smlen;
    size_t _mlen_ref, _mlen_jasmin;
    int res_ref, res_jasmin;

    for (int i = 0; i < TESTS; i++) {
        size_t mlen = MAX_MSG_LEN;
        // for (size_t mlen = 1; mlen <= MAX_MSG_LEN; mlen++) {
            if (debug) {
                printf("[xmss sign open] Test %d/%d (msg len = %ld/%d)\n", i + 1, 5, mlen, MAX_MSG_LEN);
            }

            // First we need to generate a keypair and a valid signature
            xmss_keypair(pk, sk, oid);
            xmss_sign(sk, sm, (unsigned long long *)&smlen, m, mlen);

            res_ref = xmss_sign_open_jazz(m, &_mlen_ref, sm, smlen, pk);
            res_jasmin = xmss_sign_open_jazz(m, &_mlen_jasmin, sm, smlen, pk);

            assert(_mlen_ref == mlen);
            assert(_mlen_jasmin == mlen);
            assert(_mlen_jasmin == _mlen_ref);
            assert(res_ref == 0);
            assert(res_jasmin == 0);
            assert(res_jasmin == res_ref);

            // Flip one bit which invalidates the signature
            bitflip(sm, p.sig_bytes + mlen);

            // The signature is invalid so res should be != 0
            res_ref = xmss_sign_open_jazz(m, &_mlen_ref, sm, smlen, pk);
            res_jasmin = xmss_sign_open_jazz(m, &_mlen_jasmin, sm, smlen, pk);

            assert(res_ref != 0);
            assert(res_jasmin != 0);
            assert(res_jasmin == res_ref);
        // }
    }
}

void test_xmssmt_sign_open(void) {
    bool debug = true;

    xmss_params p;
    uint32_t oid;

    if (xmssmt_str_to_oid(&oid, xstr(IMPL)) == -1) {
        fprintf(stderr, "Failed to generate oid from impl name\n");
        exit(-1);
    }

    if (xmssmt_parse_oid(&p, oid) == -1) {
        fprintf(stderr, "Failed to generate params from oid\n");
        exit(-1);
    }

    uint8_t m[MAX_MSG_LEN];
    uint8_t pk[XMSS_OID_LEN + p.pk_bytes];
    uint8_t sk[XMSS_OID_LEN + p.sk_bytes];
    uint8_t sm[p.sig_bytes + MAX_MSG_LEN];
    size_t smlen;
    size_t _mlen_ref, _mlen_jasmin;
    int res_ref, res_jasmin;

    for (int i = 0; i < TESTS; i++) {
        size_t mlen = MAX_MSG_LEN;
        // for (size_t mlen = 1; mlen <= MAX_MSG_LEN; mlen++) {
        if (debug) {
            printf("[xmssmt sign open] Test %d/%d (msg len = %ld/%d)\n", i + 1, TESTS, mlen, MAX_MSG_LEN);
        }

        // First we need to generate a keypair and a valid signature
        xmssmt_keypair(pk, sk, oid);
        xmssmt_sign(sk, sm, (unsigned long long *)&smlen, m, mlen);

        res_ref = xmssmt_sign_open_jazz(m, &_mlen_ref, sm, smlen, pk);        // Obs: Verifying does not update the SK
        res_jasmin = xmssmt_sign_open_jazz(m, &_mlen_jasmin, sm, smlen, pk);  // Obs: Verifying does not update the SK

        assert(_mlen_ref == mlen);
        assert(_mlen_jasmin == mlen);
        assert(_mlen_jasmin == _mlen_ref);
        assert(res_ref == 0);
        assert(res_jasmin == 0);
        assert(res_jasmin == res_ref);
    }
    // }
}

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

void test_xmss_api(void) {
    // Test that verification after signing works

#define XMSS_MLEN 32
#define MAX_SIGNATURES ((unsigned long long)pow(2, p.full_height) - 1)
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

    uint8_t m[XMSS_MLEN];
    size_t mlen = XMSS_MLEN;
    uint8_t pk[XMSS_OID_LEN + p.pk_bytes];
    uint8_t sk[XMSS_OID_LEN + p.sk_bytes];
    uint8_t sm[p.sig_bytes + XMSS_MLEN];
    size_t smlen;
    int res;

    for (int i = 0; i < TESTS; i++) {
        xmss_keypair_jazz(pk, sk);

        for (unsigned long long int sig = 0; sig < MAX_SIGNATURES; sig++) {
            if (debug) {
                printf("[xmss api] Test %d/%d (signature %lld/%lld)\n", i + 1, TESTS, sig + 1, MAX_SIGNATURES);
            }

            randombytes(m, XMSS_MLEN);

            // xmss_sign_jazz(sk, sm, &smlen, m, mlen);  // sk is updated here
            xmss_sign(sk, sm, (long long unsigned int *)&smlen, m, mlen);  // sk is updated here
            // res = xmss_sign_open_jazz(m, &mlen, sm, smlen, pk);
            res = xmss_sign_open(m, (long long unsigned int *)&mlen, sm, smlen, pk);

#ifdef DEBUG_TEST
            if (res != 0) {
                fprintf(stderr, "[xmss api] Test %d/%d (signature %lld/%lld) failed\n", i + 1, TESTS, sig + 1,
                        MAX_SIGNATURES);
            }
#else
            assert(res == 0);
#endif
        }
    }

#undef XMSS_MLEN
#undef MAX_SIGNATURES
}

void test_xmssmt_api(void) {
    // Test that verification after signing works

#define XMSS_MLEN 32
#define MAX_SIGNATURES (1ULL << p.full_height) - 1

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

    uint8_t m[XMSS_MLEN];
    size_t mlen = XMSS_MLEN;
    uint8_t pk[XMSS_OID_LEN + p.pk_bytes];
    uint8_t sk[XMSS_OID_LEN + p.sk_bytes];
    uint8_t sm[p.sig_bytes + XMSS_MLEN];
    size_t smlen;
    int res;

    for (int i = 0; i < TESTS; i++) {
        xmssmt_keypair_jazz(pk, sk);

        for (unsigned long long int sig = 0; sig < MAX_SIGNATURES; sig++) {
            if (debug) {
                printf("[xmssmt api] Test %d/%d (signature %lld/%lld)\n", i + 1, TESTS, sig + 1, MAX_SIGNATURES);
            }

            randombytes(m, XMSS_MLEN);

            xmssmt_sign_jazz(sk, sm, &smlen, m, mlen);
            res = xmssmt_sign_open_jazz(m, &mlen, sm, smlen, pk);

            assert(res == 0);
        }
    }

#undef XMSS_MLEN
#undef MAX_SIGNATURES
}

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

void test_xmss_sk_reuse(void) {
#define XMSS_MLEN 32

    // This test checks that the signing functions returns -2 after signing 2^h-1 messages
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

    int max_signatures = (1ULL << p.full_height) - 1;  // 2^h-1

    uint8_t m[XMSS_MLEN];
    size_t mlen = XMSS_MLEN;
    uint8_t pk[XMSS_OID_LEN + p.pk_bytes];
    uint8_t sk[XMSS_OID_LEN + p.sk_bytes];
    uint8_t sk0[XMSS_OID_LEN + p.sk_bytes];
    uint8_t sm_ref[p.sig_bytes + XMSS_MLEN];
    uint8_t sm_jasmin[p.sig_bytes + XMSS_MLEN];
    size_t smlen_ref, smlen_jasmin;
    int res_ref, res_jasmin;

    // Generate the keypair
    xmss_keypair(pk, sk, oid);
    memcpy(sk0, sk, XMSS_OID_LEN + p.sk_bytes);  // Because the sk is updated after signing

    // sign 2^h - 1 messages
    for (int i = 0; i < max_signatures; i++) {
        if (debug) {
            printf("[xmss sk reusage] Signing %d/%d msg\n", i + 1, max_signatures);
        }

        res_ref = xmss_sign(sk, sm_ref, (unsigned long long *)&smlen_ref, m, mlen);
        res_jasmin = xmss_sign_jazz(sk0, sm_jasmin, &smlen_jasmin, m, mlen);

        assert(res_ref == 0);
        assert(res_jasmin == 0);
        assert(res_jasmin == res_ref);
    }

    // check that the next time we try to sign, xmss_sign returns -2
    res_ref = xmss_sign(sk, sm_ref, (unsigned long long *)&smlen_ref, m, mlen);
    res_jasmin = xmss_sign_jazz(sk0, sm_jasmin, &smlen_jasmin, m, mlen);
    assert(res_ref == -2);
    assert(res_jasmin == -2);
    assert(res_jasmin == res_ref);

    puts("returned -2");

#undef XMSS_MLEN
}

void test_xmssmt_sk_reuse() {
    // This test checks that the signing functions returns -2 after signing 2^h messages

#define XMSS_MLEN 32

    // This test checks that the signing functions returns -2 after signing 2^h-1 messages
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

    int max_signatures = (1ULL << p.full_height) - 1;  // 2^h-1

    uint8_t m[XMSS_MLEN];
    size_t mlen = XMSS_MLEN;
    uint8_t pk[XMSS_OID_LEN + p.pk_bytes];
    uint8_t sk[XMSS_OID_LEN + p.sk_bytes];
    uint8_t sk0[XMSS_OID_LEN + p.sk_bytes];
    uint8_t sm_ref[p.sig_bytes + XMSS_MLEN];
    uint8_t sm_jasmin[p.sig_bytes + XMSS_MLEN];
    size_t smlen_ref, smlen_jasmin;
    int res_ref, res_jasmin;

    // Generate the keypair
    xmssmt_keypair(pk, sk, oid);
    memcpy(sk0, sk, XMSS_OID_LEN + p.sk_bytes);  // Because the sk is updated after signing

    // sign 2^h - 1 messages
    for (int i = 0; i < max_signatures; i++) {
        if (debug) {
            printf("[xmss sk reusage] Signing %d/%d msg\n", i + 1, max_signatures);
        }

        res_ref = xmssmt_sign(sk, sm_ref, (unsigned long long *)&smlen_ref, m, mlen);
        res_jasmin = xmssmt_sign_jazz(sk0, sm_jasmin, &smlen_jasmin, m, mlen);

        assert(res_ref == 0);
        assert(res_jasmin == 0);
        assert(res_jasmin == res_ref);
    }

    // check that the next time we try to sign, xmss_sign returns -2
    res_ref = xmssmt_sign(sk, sm_ref, (unsigned long long *)&smlen_ref, m, mlen);
    res_jasmin = xmssmt_sign_jazz(sk0, sm_jasmin, &smlen_jasmin, m, mlen);
    assert(res_ref == -2);
    assert(res_jasmin == -2);
    assert(res_jasmin == res_ref);

#undef XMSS_MLEN
}

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

void test_xmss_invalid_signature() {
    // This test checks that the verifying function rejects invalid signatures

#define XMSS_MLEN 32

    // This test checks that the signing functions returns -2 after signing 2^h-1 messages
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

    uint8_t m[XMSS_MLEN];
    size_t mlen = XMSS_MLEN;
    uint8_t pk[XMSS_OID_LEN + p.pk_bytes];
    uint8_t sk[XMSS_OID_LEN + p.sk_bytes];
    uint8_t sm[p.sig_bytes + XMSS_MLEN];
    size_t smlen;
    int res;

    for (int i = 0; i < TESTS; i++) {
        if (debug) {
            printf("[xmss invalid signature] Test %d/%d\n", i + 1, TESTS);
        }

        // Generate key pair and sign a message
        xmss_keypair_jazz(pk, sk);
        xmss_sign_jazz(sk, sm, &smlen, m, mlen);

        // Flip one bit which invalidates the signature
        bitflip(sm, p.sig_bytes + XMSS_MLEN);

        // Verification should now fail
        res = xmss_sign_open_jazz(m, &mlen, sm, smlen, pk);

        assert(res != 0);
    }

#undef XMSS_MLEN
}

void test_xmssmt_invalid_signature() {
    // This test checks that the verifying function rejects invalid signatures

#define XMSS_MLEN 32

    // This test checks that the signing functions returns -2 after signing 2^h-1 messages
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

    uint8_t m[XMSS_MLEN];
    size_t mlen = XMSS_MLEN;
    uint8_t pk[XMSS_OID_LEN + p.pk_bytes];
    uint8_t sk[XMSS_OID_LEN + p.sk_bytes];
    uint8_t sm[p.sig_bytes + XMSS_MLEN];
    size_t smlen;
    int res;

    for (int i = 0; i < TESTS; i++) {
        if (debug) {
            printf("[xmssmt invalid signature] Test %d/%d\n", i + 1, TESTS);
        }

        // Generate key pair and sign a message
        xmssmt_keypair_jazz(pk, sk);
        xmssmt_sign_jazz(sk, sm, &smlen, m, mlen);

        // Flip one bit which invalidates the signature
        bitflip(sm, p.sig_bytes + XMSS_MLEN);

        // Verification should now fail
        res = xmssmt_sign_open_jazz(m, &mlen, sm, smlen, pk);

        assert(res != 0);
    }

#undef XMSS_MLEN
}

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

int main(void) {
    test_randombytes();

    puts("=========================================================================================");
    printf("Running tests for: %s\n", xstr(IMPL));

    if (starts_with(xstr(IMPL), "XMSSMT")) {
        puts("Multi tree variant");
        test_xmssmt_keypair();    // OK
        test_xmssmt_sign();       // OK
        test_xmssmt_sign_open();  // OK
        // test_xmssmt_api();
        // test_xmssmt_sk_reuse();
        // test_xmssmt_invalid_signature();
    } else {
        puts("Single tree variant");
        test_xmss_keypair();    // OK
        test_xmss_sign();       // OK
        test_xmss_sign_open();  // OK
        // test_xmss_api();
        // test_xmss_sk_reuse();
        // test_xmss_invalid_signature();
    }

    puts("=========================================================================================");

    return 0;
}
