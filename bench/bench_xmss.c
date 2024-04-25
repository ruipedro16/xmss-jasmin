#include <assert.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "cpucycles.c"
#include "macros.h"
#include "params.h"
#include "xmss.h"

#ifndef IMPL
#error IMPL not defined
#endif

#ifndef MAX_MSG_LEN
#define MAX_MSG_LEN 1024
#endif

#ifndef TIMINGS
#define TIMINGS 100
#endif

#ifndef LOOPS
#define LOOPS 10
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

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

void bench_xmss(void) {
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

}

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

void bench_xmssmt(void) {
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
    size_t mlen, smlen;

    // Warmup
    for (int i = 0; i < 10; i++) {
        xmss_keypair_jazz(pk, sk);
        xmss_sign_jazz(sk, sm, &smlen, m, MAX_MSG_LEN);
        xmss_sign_open_jazz(m, &mlen, sm, smlen, pk);
    }

    puts("Finished Warmup")
}

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

int main(void) {
    starts_with(xstr(IMPL), "XMSSMT") ? bench_xmssmt() : bench_xmss();
    printf("Finished running benchmarks for %s\n", xstr(IMPL));
    return 0;
}