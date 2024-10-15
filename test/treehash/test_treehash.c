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
#include "randombytes.h"
#include "xmss.h"
#include "xmss_core.h"

#ifndef TESTS
#define TESTS 10
#endif

static int starts_with(const char *str, const char *prefix) { return strncmp(str, prefix, strlen(prefix)) == 0; }

extern uint8_t treehash_cond_jazz(const uint32_t *, uint64_t);

static uint64_t randombytes_interval(uint64_t min, uint64_t max) {
    assert(min <= max);

    uint64_t range = max - min;
    uint64_t random_value;

    // Generate a random value within the range
    do {
        random_value = (uint64_t)rand();
    } while (random_value >= ((uint64_t)RAND_MAX + 1 - ((uint64_t)RAND_MAX + 1) % range));

    return min + (random_value % range);
}

void test_condition(const xmss_params *p) {
    assert(p);

    bool debug = true;

    uint64_t offset;
    uint32_t heights[p->tree_height + 1];

    if (false) {
        printf("Tree height: %d\n", p->tree_height);
    }

    uint8_t res;

    // Caso 1: Offset >= 2 e verdadeiro => a segunda parte da conjuncao e avaliada (provavelmente e false)
    for (int i = 0; i < TESTS; i++) {
        if (debug) {
            printf("Treehash Condition #0: Test %d/%d (true /\\ ...)\n", i + 1, TESTS);
        }

        offset = randombytes_interval(2, p->tree_height);

        assert(offset >= 2);
        assert(offset < p->tree_height + 1);

        randombytes((uint8_t *)heights, (p->tree_height + 1) * sizeof(uint32_t));

        res = treehash_cond_jazz(heights, offset);
        assert(heights[offset - 1] == heights[offset - 2] ? res == 1 : res == 0);
    }

    // Caso 2: Offset >= 2 e verdadeiro => a segunda parte da conjuncao e avaliada (vai ser verdadeira)
    for (int i = 0; i < TESTS; i++) {
        if (debug) {
            printf("Treehash Condition #1: Test %d/%d (true /\\ ...)\n", i + 1, TESTS);
        }

        offset = randombytes_interval(2, p->tree_height);

        assert(offset >= 2);
        assert(offset < p->tree_height + 1);

        randombytes((uint8_t *)heights, (p->tree_height + 1) * sizeof(uint32_t));
        heights[offset - 1] = heights[offset - 2];  // Ensures the 2nd part of && is true

        res = treehash_cond_jazz(heights, offset);
        assert(heights[offset - 1] == heights[offset - 2] ? res == 1 : res == 0);
    }

    // Caso 3: Offset < 2 e verdadeiro => a segunda parte da conjuncao nao e avaliada
    for (int i = 0; i < TESTS; i++) {
        if (debug) {
            printf("Treehash Condition #2: Test %d/%d (false /\\ ...)\n", i + 1, TESTS);
        }

        offset = randombytes_interval(0, 1);

        assert(offset < 2);
        /* assert(offset >= 0); */ /* warning: comparison of unsigned expression in ‘>= 0’ is always true */

        randombytes((uint8_t *)heights, (p->tree_height + 1) * sizeof(uint32_t));

        res = treehash_cond_jazz(heights, offset);
        assert(res == 0);
    }
}

void test_api(xmss_params *p) {
#define XMSS_MLEN 32
    bool debug = true;

    uint8_t pk_ref[p->pk_bytes];
    uint8_t pk_test[p->pk_bytes];

    uint8_t sk_ref[p->sk_bytes];
    uint8_t sk_test[p->sk_bytes];

    uint8_t seed[3 * p->n];

    unsigned char m_ref[XMSS_MLEN], m_new[XMSS_MLEN];
    unsigned char sm_ref[p->sig_bytes + XMSS_MLEN], sm_new[p->sig_bytes + XMSS_MLEN];
    unsigned long long smlen_ref, smlen_new;

    for (size_t i = 0; i < 3 * p->n; i++) {
        seed[i] = 42;
    }

    // Test KG
    for (int i = 0; i < TESTS; i++) {
        if (debug) {
            printf("KG: Test %d/%d\n", i + 1, TESTS);
        }

        xmssmt_core_seed_keypair(p, pk_ref, sk_ref, seed);
        xmssmt_core_seed_keypair_new(p, pk_test, sk_test, seed);

        assert(memcmp(pk_ref, pk_test, p->pk_bytes) == 0);
        assert(memcmp(sk_ref, sk_test, p->sk_bytes) == 0);
    }

    // Test Sign
    for (int i = 0; i < TESTS; i++) {
        if (debug) {
            printf("KG: Sign %d/%d\n", i + 1, TESTS);
        }

        // First we generate a keypair to sign
        xmssmt_core_seed_keypair(p, pk_ref, sk_ref, seed);

        memcpy(sk_test, sk_ref, p->sk_bytes);

        assert(memcmp(sk_ref, sk_test, p->sk_bytes) == 0);  // Make sure the keypair is the same (we only need the sk)

        xmssmt_core_sign(p, sk_ref, sm_ref, &smlen_ref, m_ref, XMSS_MLEN);
        xmssmt_core_sign_new(p, sk_test, sm_new, &smlen_new, m_new, XMSS_MLEN);

        assert(memcmp(sk_test, sk_ref, p->sk_bytes) == 0);
        assert(smlen_new == smlen_ref);
    }

    // OBS: We dont test verify because it does not depend on treehash

#undef XMSS_MLEN
}

int main(void) {
    xmss_params p;
    uint32_t oid;
    const char impl[] = "XMSS-SHA2_10_256";

    if (starts_with(impl, "XMSSMT")) {
        if (xmssmt_str_to_oid(&oid, impl) == -1) {
            fprintf(stderr, "[multi tree]: Failed to generate oid from impl name\n");
            exit(-1);
        }

        if (xmssmt_parse_oid(&p, oid) == -1) {
            fprintf(stderr, "[multi tree]: Failed to generate params from oid\n");
            exit(-1);
        }
    } else {
        if (xmss_str_to_oid(&oid, impl) == -1) {
            fprintf(stderr, "[single tree]: Failed to generate oid from impl name\n");
            exit(-1);
        }

        if (xmss_parse_oid(&p, oid) == -1) {
            fprintf(stderr, "[single tree]: Failed to generate params from oid\n");
            exit(-1);
        }
    }

    // test_condition(&p);
    test_api(&p);

    return 0;
}