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

#ifndef TESTS
#define TESTS 100
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

void test_condition(xmss_params *p) {
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

    test_condition(&p);

    return 0;
}