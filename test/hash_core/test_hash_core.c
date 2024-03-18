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

#ifndef INLEN
#error INLEN not defined
#endif

#ifndef TESTS
#define TESTS 10000
#endif

#define core_hash_shake256_out_64_jazz NAMESPACE1(core_hash_shake256_out_64_jazz, INLEN)
extern void core_hash_shake256_out_64_jazz(const uint8_t *, uint8_t *);

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// REF IMPL
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
static int core_hash_ref(const xmss_params *params, unsigned char *out, const unsigned char *in,
                         unsigned long long inlen) {
    unsigned char buf[64];

    if (params->n == 24 && params->func == XMSS_SHA2) {
        SHA256(in, inlen, buf);
        memcpy(out, buf, 24);
    } else if (params->n == 24 && params->func == XMSS_SHAKE256) {
        shake256(out, 24, in, inlen);
    } else if (params->n == 32 && params->func == XMSS_SHA2) {
        SHA256(in, inlen, out);
    } else if (params->n == 32 && params->func == XMSS_SHAKE128) {
        shake128(out, 32, in, inlen);
    } else if (params->n == 32 && params->func == XMSS_SHAKE256) {
        shake256(out, 32, in, inlen);
    } else if (params->n == 64 && params->func == XMSS_SHA2) {
        SHA512(in, inlen, out);
    } else if (params->n == 64 && params->func == XMSS_SHAKE256) {
        shake256(out, 64, in, inlen);
    } else {
        return -1;
    }
    return 0;
}
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

void test_core_hash_shake256_out_64(void) {
    bool debug = false;

    uint8_t out_ref[64], out_jazz[64];
    uint8_t in[INLEN];

    xmss_params p;
    uint32_t oid;

    if (xmss_str_to_oid(&oid, "XMSS-SHAKE_20_512") == -1) {
        fprintf(stderr, "Failed to generate oid from impl name\n");
        exit(-1);
    }

    if (xmss_parse_oid(&p, oid) == -1) {
        fprintf(stderr, "Failed to generate params from oid\n");
        exit(-1);
    }

    assert(p.n == 64);
    assert(p.func == XMSS_SHAKE256);

    for (int i = 0; i < TESTS; i++) {
        if (debug) {
            printf("[core_hash_shake256_out_64] Test %d/%d\n", i, TESTS);
        }

        randombytes(in, INLEN);

        core_hash_shake256_out_64_jazz(in, out_jazz);
        core_hash_ref(&p, out_ref, in, INLEN);

        assert(memcmp(out_ref, out_jazz, 64) == 0);
    }
}

int main(void) {
    test_core_hash_shake256_out_64();
    printf("Hash Core {INLEN=%d}: OK\n", INLEN);
    return 0;
}