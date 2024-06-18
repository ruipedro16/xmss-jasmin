#include <assert.h>
#include <inttypes.h>
#include <math.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "fips202.h"
#include "macros.h"
#include "params.h"
#include "randombytes.h"
#include "utils.h"
#include "xmss.h"
#include "xmss_commons.h"
#include "xmss_core.h"

#ifndef IMPL
#error IMPL not defined
#endif

#ifndef N
#define N 500
#endif

static int starts_with(const char *str, const char *prefix) { return strncmp(str, prefix, strlen(prefix)) == 0; }

void print_hex(unsigned char *buf, int len) {
    for (int i = 0; i < len; i++) {
        printf("%x%x", buf[i] / 16, buf[i] & 15);
    }
}

void print_hash(unsigned char *buf, int len) {
    unsigned char tmp[10];
    shake128(tmp, 10, buf, len);
    print_hex(tmp, 10);
}

void vectors_xmss(void) {
    bool debug = true;

    xmss_params params;
    uint32_t oid;

    if (xmss_str_to_oid(&oid, xstr(IMPL)) == -1) {
        fprintf(stderr, "Failed to generate oid from impl name\n");
        exit(-1);
    }

    if (xmss_parse_oid(&params, oid) == -1) {
        fprintf(stderr, "Failed to generate params from oid\n");
        exit(-1);
    }

    unsigned char seed[params.n * 3];
    unsigned char pk[params.pk_bytes];
    unsigned char sk[params.sk_bytes];
    unsigned char msg[1] = {37};
    unsigned char sm[params.sig_bytes + 1];
    unsigned long long smlen = 0;

    int mt = starts_with(xstr(IMPL), "XMSSMT");

    for (int i = 0; i < N; i++) {
        if (debug) {
            fprintf(stderr, "%d/%d\n", i + 1, N);
        }

        randombytes((uint8_t*)seed, params.n * 3);

        xmssmt_core_seed_keypair(&params, pk, sk, seed);

        ull_to_bytes(sk, params.index_bytes, 1 << (params.full_height - 1));

        if (mt) {
            xmssmt_core_sign(&params, sk, sm, &smlen, msg, 1);
        } else {
            xmss_core_sign(&params, sk, sm, &smlen, msg, 1);
        }

        if (mt) {
            printf("XMSSMT ");
        } else {
            printf("XMSS ");
        }

        printf("%d ", oid);
        printf(" ");
        print_hash(seed, 3 * params.n);
        printf(" ");
        print_hash(pk, params.pk_bytes);
        printf(" ");
        print_hash(sm, params.sig_bytes);
        printf("\n");
    }
}

int main(void) { vectors_xmss(); return 0; }