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
#define TIMINGS 20
#endif

#ifndef LOOPS
#define LOOPS 10
#endif

// TODO: extern void go here

static void print_results(FILE *f, int loop, size_t message_len, const char *function, uint64_t cycles_ref[TIMINGS],
                          uint64_t cycles_jasmin[TIMINGS]) {
    if (!f) {
        fprintf(stderr, "FILE *f is NULL in print_results\n");
        exit(-1);
    }

    if (!function) {
        fprintf(stderr, "char* function is NULL in print_results\n");
    }

#ifdef ALL_TIMINGS
    cpucycles_median(cycles_ref, TIMINGS);
    cpucycles_median(cycles_jasmin, TIMINGS);

    for (size_t i = 0; i < TIMINGS - 1; i++) {
        uint64_t diff = cycles_jasmin[i] - cycles_ref[i];
        fprintf(f, "%d,%s,%ld,%ld,%ld,%ld\n", loop, function, message_len, cycles_ref[i], cycles_jasmin[i], diff);
    }
#else
    uint64_t median_ref = cpucycles_median(cycles_ref, TIMINGS);
    uint64_t median_jasmin = cpucycles_median(cycles_jasmin, TIMINGS);
    uint64_t diff = median_jasmin - median_ref;  // TODO: Can I compute it like this?
    fprintf(f, "%d,%s,%ld,%ld,%ld,%ld\n", loop, function, message_len, median_ref, median_jasmin, diff);
#endif
}

int main(void) {
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

    FILE *f;
    if ((f = fopen("csv/bench_xmss.csv", "w")) == NULL) {
        fprintf(stderr, "Failed to open file csv/bench_xmss.csv\n");
        exit(-1);
    }

    fprintf(f, "Loop,Function,MessageLen,Reference,Jasmin,Diff\n");

    uint64_t cycles_ref[LOOPS][TIMINGS], cycles_jasmin[LOOPS][TIMINGS];

    uint8_t pk[XMSS_OID_LEN + p.pk_bytes];
    uint8_t sk[XMSS_OID_LEN + p.sk_bytes];
    uint8_t m[MAX_MSG_LEN];
    uint8_t sm[p.sig_bytes + 1];
    unsigned long long smlen = 0;

    for (int i = 0; i < 10; i++) {
        // warmup
    }

    // TODO:

    for (int loop = 0; loop < LOOPS; loop++) {
        for (size_t message_len = 1; message_len <= MAX_MSG_LEN; message_len++) {
            if (debug) {
                printf("[MessageLen=%ld]: Loop iteration: %d\n", message_len, loop);
            }

            // XMSS_KEYPAIR [ref]
            for (int i = 0; i < TIMINGS; i++) {
                cycles_ref[loop][i] = cpucycles();
                xmss_keypair(pk, sk, oid);
            }

            // XMSS_KEYPAIR [jasmin]
            for (int i = 0; i < TIMINGS; i++) {
                cycles_jasmin[loop][i] = cpucycles();
                // TODO:
                // xmss_keypair_jazz(pk, sk);
            }

            print_results(f, loop, message_len, "xmss_keypair", cycles_ref[loop], cycles_jasmin[loop]);

            // XMSS_SIGN [ref]
            for (int i = 0; i < TIMINGS; i++) {
                cycles_ref[loop][i] = cpucycles();
                xmss_sign(sk, sm, &smlen, m, message_len);
            }

            // XMSS_SIGN [jasmin]
            for (int i = 0; i < TIMINGS; i++) {
                cycles_jasmin[loop][i] = cpucycles();
                // TODO:
                // xmss_sign_jazz(sk, sm, &smlen, m, message_len);
            }

            print_results(f, loop, message_len, "xmss_sign", cycles_ref[loop], cycles_jasmin[loop]);

            // XMSS_SIGN [ref]
            for (int i = 0; i < TIMINGS; i++) {
                cycles_ref[loop][i] = cpucycles();
                xmss_sign_open(m, (unsigned long long *)&message_len, sm, smlen, pk);
            }

            // XMSS_SIGN [jasmin]
            for (int i = 0; i < TIMINGS; i++) {
                cycles_jasmin[loop][i] = cpucycles();
                // TODO:
                // xmss_sign_open_jazz(m, &message_len, sm, smlen, pk);
            }

            print_results(f, loop, message_len, "xmss_sign_open", cycles_ref[loop], cycles_jasmin[loop]);

            // XMSSMT_KEYPAIR [ref]
            for (int i = 0; i < TIMINGS; i++) {
                cycles_ref[loop][i] = cpucycles();
                xmssmt_keypair(pk, sk, oid);
            }

            // XMSSMT_KEYPAIR [jasmin]
            for (int i = 0; i < TIMINGS; i++) {
                cycles_jasmin[loop][i] = cpucycles();
                // TODO:
                // xmssmt_keypair_jazz(pk, sk);
            }

            print_results(f, loop, message_len, "xmssmt_keypair", cycles_ref[loop], cycles_jasmin[loop]);

            // XMSSMT_SIGN [ref]
            for (int i = 0; i < TIMINGS; i++) {
                cycles_ref[loop][i] = cpucycles();
                xmssmt_sign(sk, sm, &smlen, m, message_len);
            }

            // XMSSMT_SIGN [jasmin]
            for (int i = 0; i < TIMINGS; i++) {
                cycles_jasmin[loop][i] = cpucycles();
                // TODO:
                // xmssmt_sign_jazz(sk, sm, &smlen, m, message_len);
            }

            print_results(f, loop, message_len, "xmssmt_sign", cycles_ref[loop], cycles_jasmin[loop]);

            // XMSSMT_SIGN [ref]
            for (int i = 0; i < TIMINGS; i++) {
                cycles_ref[loop][i] = cpucycles();
                xmssmt_sign_open(m, (unsigned long long *)&message_len, sm, smlen, pk);
            }

            // XMSSMT_SIGN [jasmin]
            for (int i = 0; i < TIMINGS; i++) {
                cycles_jasmin[loop][i] = cpucycles();
                // TODO:
                // xmssmt_sign_open_jazz(m, &message_len, sm, smlen, pk);
            }

            print_results(f, loop, message_len, "xmssmt_sign_open", cycles_ref[loop], cycles_jasmin[loop]);
        }
    }

    return 0;
}