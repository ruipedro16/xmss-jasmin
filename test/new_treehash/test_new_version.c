#include <assert.h>
#include <inttypes.h>
#include <math.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "macros.h"
#include "new_xmss.h"
#include "params.h"
#include "print.h"
#include "xmss_core.h"

#ifndef TESTS
#define TESTS 1
#endif

static int starts_with(const char *str, const char *prefix) { return strncmp(str, prefix, strlen(prefix)) == 0; }

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

void test_kg(xmss_params p) {
    bool debug = true;

    uint8_t pk_ref[p.pk_bytes];
    uint8_t sk_ref[p.sk_bytes];

    uint8_t pk_new[p.pk_bytes];
    uint8_t sk_new[p.sk_bytes];

    uint8_t seed[3 * p.n];

    for (size_t i = 0; i < 3 * p.n; i++) {
        seed[i] = 42;
    }

    for (int i = 0; i < TESTS; i++) {
        if (debug) {
            printf("KeyGen: Test %d/%d\n", i + 1, TESTS);
        }

        xmssmt_core_seed_keypair(&p, pk_ref, sk_ref, seed);
        xmssmt_core_seed_keypair_new(&p, pk_new, sk_new, seed);

        assert(memcmp(pk_new, pk_ref, p.pk_bytes) == 0);
        assert(memcmp(sk_new, sk_ref, p.sk_bytes) == 0);
    }
}

void test_sign(xmss_params p) {
#define XMSS_MLEN 20

    bool debug = true;

    uint8_t pk_ref[p.pk_bytes];
    uint8_t sk_ref[p.sk_bytes];

    uint8_t pk_new[p.pk_bytes];
    uint8_t sk_new[p.sk_bytes];

    uint8_t seed[3 * p.n];

    for (size_t i = 0; i < 3 * p.n; i++) {
        seed[i] = 42;
    }

    unsigned char m_ref[XMSS_MLEN], m_new[XMSS_MLEN];
    unsigned char sm_ref[p.sig_bytes + XMSS_MLEN], sm_new[p.sig_bytes + XMSS_MLEN];
    unsigned long long smlen_ref, smlen_new;

    for (size_t i = 0; i < XMSS_MLEN; i++) {
        m_ref[i] = 42;
        m_new[i] = 42;
    }

    for (int i = 0; i < TESTS; i++) {
        if (debug) {
            printf("Sign: Test %d/%d\n", i + 1, TESTS);
        }

        xmssmt_core_seed_keypair(&p, pk_ref, sk_ref, seed);
        xmssmt_core_seed_keypair_new(&p, pk_new, sk_new, seed);

        memset(sm_new, 0, p.sig_bytes + XMSS_MLEN);
        memset(sm_ref, 0, p.sig_bytes + XMSS_MLEN);

        assert(memcmp(sk_new, sk_ref, p.sk_bytes) == 0);
        assert(memcmp(m_ref, m_new, XMSS_MLEN) == 0);

        xmssmt_core_sign(&p, sk_ref, sm_ref, &smlen_ref, m_ref, XMSS_MLEN);
        xmssmt_core_sign_new(&p, sk_new, sm_new, &smlen_new, m_new, XMSS_MLEN);

        assert(memcmp(sk_new, sk_ref, p.sk_bytes) == 0);
        assert(smlen_new == smlen_ref);

        // printf("tree height = %d\n", p.tree_height);
        // printf("full height = %d\n", p.full_height);

        if (memcmp(sm_new, sm_ref, p.sig_bytes + XMSS_MLEN) != 0) {
            puts("==============================================================================================");
            // fprint_str_u8("sm_new.txt", "sm", sm_new, p.sig_bytes);
            // fprint_str_u8("sm_ref.txt", "sm", sm_ref, p.sig_bytes);
            printf("Signature Preffix length: %ld\n", longestCommonPrefixSize(sm_ref, sm_new, p.sig_bytes + XMSS_MLEN));
            puts("==============================================================================================");

            // idx : 4 bytes
            // fprint_str_u8("idx.txt", "sm", sm_new, p.index_bytes);
            // fprint_str_u8("idx.txt", "sm", sm_ref, p.index_bytes);
            assert(memcmp(sm_ref, sm_new, p.index_bytes) == 0);
            puts("Index OK");

            puts("==============================================================================================");

            // R : 32 bytes
            // fprint_str_u8("R.txt", "sm", sm_new + p.index_bytes, p.n);
            // fprint_str_u8("R.txt", "sm", sm_ref + p.index_bytes, p.n);
            assert(memcmp(sm_ref + p.index_bytes, sm_new + p.index_bytes, p.n) == 0);
            puts("R OK");

            puts("==============================================================================================");

            // The rest of the signature is WOTS SIG || AUTH PATH only for the single tree variant
            // for the multi tree variant, it is WOTS SIG || AUTH PATH || WOTS SIG || AUTH PATH || WOTS SIG || AUTH PATH
            // ......
            if (p.pk_bytes == 1) {
                // wots signature :
                assert(p.wots_sig_bytes == p.n * p.wots_len);

                for (unsigned int k = 0; k < p.wots_len; k++) {
                    // puts("==============================================================================================");
                    // printf("Testing k=%d\n", k);
                    // fprint_str_u8("wots_sig.txt", "sm", sm_new + p.index_bytes + p.n + (k * p.n), p.n);
                    // fprint_str_u8("wots_sig.txt", "sm", sm_ref + p.index_bytes + p.n + (k * p.n), p.n);
                    assert(memcmp(sm_new + p.index_bytes + p.n + (k * p.n), sm_ref + p.index_bytes + p.n + (k * p.n),
                                  p.n) == 0);
                    // printf("%d-esima parte da assinatura: OK\n", k);
                    // puts("==============================================================================================");
                }

                assert(memcmp(sm_new + p.index_bytes + p.n, sm_ref + p.index_bytes + p.n, p.wots_sig_bytes) == 0);
                puts("Wots Sig: OK");
                puts("==============================================================================================");

                // auth path :
                printf("Auth Path Preffix length: %ld\n",
                       longestCommonPrefixSize(sm_new + p.index_bytes + p.n + p.wots_sig_bytes,
                                               sm_ref + p.index_bytes + p.n + p.wots_sig_bytes, p.tree_height * p.n));

                if (memcmp(sm_new + p.index_bytes + p.n + p.wots_sig_bytes,
                           sm_ref + p.index_bytes + p.n + p.wots_sig_bytes, p.tree_height * p.n) != 0) {
                    fprint_str_u8("auth_path_ref.txt", "auth path ref", sm_ref + p.index_bytes + p.n + p.wots_sig_bytes,
                                  p.tree_height * p.n);
                    fprint_str_u8("auth_path_new.txt", "auth path new", sm_ref + p.index_bytes + p.n + p.wots_sig_bytes,
                                  p.tree_height * p.n);
                }

                assert(memcmp(sm_new + p.index_bytes + p.n + p.wots_sig_bytes,
                              sm_ref + p.index_bytes + p.n + p.wots_sig_bytes, p.tree_height * p.n) == 0);

                // At last, we assert that the whole signature is the same on both sides
                assert(memcmp(sm_new, sm_ref, p.sig_bytes + XMSS_MLEN) == 0);
            } else {
                assert(memcmp(sm_new, sm_ref, p.sig_bytes + XMSS_MLEN) == 0);
            }
        }

        assert(memcmp(sm_new, sm_ref, p.sig_bytes + XMSS_MLEN) == 0);
    }

#undef XMSS_MLEN
}

int main() {
    bool debug = true;

    xmss_params p;
    uint32_t oid;

    // char *impls[] = {"XMSS-SHA2_10_256", "XMSS-SHA2_10_192", "XMSSMT-SHA2_20/2_256", "XMSSMT-SHA2_20/4_256"};
    char *impls[] = {"XMSSMT-SHA2_20/2_256"};

    size_t impl_count = 4;

    for (size_t i = 0; i < impl_count; i++) {
        if (starts_with(impls[i], "XMSSMT")) {
            if (xmssmt_str_to_oid(&oid, impls[i]) == -1) {
                fprintf(stderr, "[multi tree]: Failed to generate oid from impl name\n");
                exit(-1);
            }

            if (xmssmt_parse_oid(&p, oid) == -1) {
                fprintf(stderr, "[multi tree]: Failed to generate params from oid\n");
                exit(-1);
            }
        } else {
            if (xmss_str_to_oid(&oid, impls[i]) == -1) {
                fprintf(stderr, "[single tree]: Failed to generate oid from impl name\n");
                exit(-1);
            }

            if (xmss_parse_oid(&p, oid) == -1) {
                fprintf(stderr, "[single tree]: Failed to generate params from oid\n");
                exit(-1);
            }
        }

        if (debug) {
            puts("=====================================================================================");
            printf("TESTING IMPL: %s\n", impls[i]);
        }

        test_kg(p);
        // test_sign(p);

        if (debug) {
            puts("=====================================================================================");
        }
    }

    return 0;
}