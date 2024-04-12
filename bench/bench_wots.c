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
#include "wots.h"

#ifndef IMPL
#error IMPL not defined
#endif

#ifndef TIMINGS
#define TIMINGS 10000
#endif

#ifndef LOOPS
#define LOOPS 1
#endif

extern void wots_pkgen_jazz(uint8_t *, const uint8_t *, const uint8_t *, uint32_t *);
extern void wots_sign_jazz(uint8_t *, const uint8_t *, const uint8_t *, const uint8_t *, uint32_t *);
extern void wots_pk_from_sig_jazz(uint8_t *pk, const uint8_t *sig, const uint8_t *msg, const uint8_t *pub_seed,
                                  uint32_t *);

static void print_results(FILE *f, int loop, const char *function, uint64_t cycles_ref[TIMINGS],
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
        fprintf(f, "%d,%s,%ld,%ld,%ld\n", loop, function, cycles_ref[i], cycles_jasmin[i], diff);
    }
#else
    uint64_t median_ref = cpucycles_median(cycles_ref, TIMINGS);
    uint64_t median_jasmin = cpucycles_median(cycles_jasmin, TIMINGS);
    uint64_t diff = median_jasmin - median_ref;  // TODO: Can I compute it like this?
    fprintf(f, "%d,%s,%ld,%ld,%ld\n", loop, function, median_ref, median_jasmin, diff);
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

#ifdef ALL_TIMINGS
    const char *filename = "csv/bench_wots_all_timings.csv";
#else
    const char *filename = "csv/bench_wots.csv";
#endif

    FILE *f;
    if ((f = fopen(filename, "w")) == NULL) {
        fprintf(stderr, "Failed to open file csv/bench_wots.csv\n");
        exit(-1);
    }

    fprintf(f, "Loop,Function,Reference,Jasmin,Diff\n");

    uint64_t cycles_ref[LOOPS][TIMINGS], cycles_jasmin[LOOPS][TIMINGS];

    uint8_t seed[p.n];
    uint8_t pub_seed[p.n];
    uint8_t pk[p.wots_sig_bytes];
    uint8_t sig[p.wots_sig_bytes];
    uint8_t m[p.n];
    uint32_t addr[8] = {0};

    for (int i = 0; i < 10; i++) {
        // warmup
        wots_pkgen(&p, pk, seed, pub_seed, addr);
        wots_sign(&p, sig, m, seed, pub_seed, addr);
        wots_pk_from_sig(&p, pk, sig, m, pub_seed, addr);

        wots_pkgen_jazz(pk, seed, pub_seed, addr);
        wots_sign_jazz(sig, m, seed, pub_seed, addr);
        wots_pk_from_sig_jazz(pk, sig, m, pub_seed, addr);
    }

    for (int loop = 0; loop < LOOPS; loop++) {
        if (debug) {
            printf("Loop: %d\n", loop);
        }

        // WOTS_PK_GEN [ref]
        for (int i = 0; i < TIMINGS; i++) {
            cycles_ref[loop][i] = cpucycles();
            wots_pkgen(&p, pk, seed, pub_seed, addr);
        }

        // WOTS_PK_GEN [jasmin]
        for (int i = 0; i < TIMINGS; i++) {
            cycles_jasmin[loop][i] = cpucycles();
            wots_pkgen_jazz(pk, seed, pub_seed, addr);
        }

        print_results(f, loop, "pkgen", cycles_ref[loop], cycles_jasmin[loop]);

        if (debug) {
            printf("Benched PK_Gen\n");
        }

        // WOTS_Sign [ref]
        for (int i = 0; i < TIMINGS; i++) {
            cycles_ref[loop][i] = cpucycles();
            wots_sign(&p, sig, m, seed, pub_seed, addr);
        }

        // WOTS_Sign [jasmin]
        for (int i = 0; i < TIMINGS; i++) {
            cycles_jasmin[loop][i] = cpucycles();
            wots_sign_jazz(sig, m, seed, pub_seed, addr);
        }

        print_results(f, loop, "sign", cycles_ref[loop], cycles_jasmin[loop]);

        if (debug) {
            printf("Benched Sign\n");
        }

        // WOTS_PKFromSig [ref]
        for (int i = 0; i < TIMINGS; i++) {
            cycles_ref[loop][i] = cpucycles();
            wots_pk_from_sig(&p, pk, sig, m, pub_seed, addr);
        }

        // WOTS_PKFromSig [jasmin]
        for (int i = 0; i < TIMINGS; i++) {
            cycles_jasmin[loop][i] = cpucycles();
            wots_pk_from_sig_jazz(pk, sig, m, pub_seed, addr);
        }

        print_results(f, loop, "pk_from_sig", cycles_ref[loop], cycles_jasmin[loop]);

        if (debug) {
            printf("Benched PKFromSig\n");
        }
    }

    fclose(f);

    return 0;
}