#include <inttypes.h>
#include <openssl/sha.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "cpucycles.c"
#include "macros.h"

#ifndef TIMINGS
#define TIMINGS 100
#endif

#ifndef LOOPS
#define LOOPS 10
#endif

#ifndef MAX_INLEN
#define MAX_INLEN 1024
#endif

#ifndef FILENAME
#define FILENAME "csv/bench_sha2_ptr.csv"
#endif

extern void sha256_in_ptr_jazz(uint8_t *out, uint8_t *in, size_t inlen);

static void print_results(FILE *f, size_t inlen, int loop, uint64_t cycles_ref[TIMINGS],
                          uint64_t cycles_jasmin[TIMINGS]) {
    if (!f) {
        fprintf(stderr, "FILE *f is NULL in print_results\n");
        exit(-1);
    }

    cpucycles_median(cycles_ref, TIMINGS);
    cpucycles_median(cycles_jasmin, TIMINGS);

    for (size_t i = 0; i < TIMINGS; i++) {
        fprintf(f, "%ld,%d,%ld,%ld\n", inlen, loop, cycles_ref[i], cycles_jasmin[i]);
    }
}

int main(void) {
    FILE *f;
    if ((f = fopen(FILENAME, "w")) == NULL) {
        fprintf(stderr, "Failed to open file %s\n", FILENAME);
        exit(-1);
    }

    fprintf(f, "Inlen,Loop,Reference,Jasmin\n");  // Header of the csv

    uint8_t in[MAX_INLEN];
    uint8_t out[SHA256_DIGEST_LENGTH];

    uint64_t cycles_ref[LOOPS][TIMINGS];
    uint64_t cycles_jasmin[LOOPS][TIMINGS];

    // warmup
    for (int t = 0; t < TIMINGS; t++) {
        sha256_in_ptr_jazz(out, in, 42);
        SHA256(in, 42, out);
    }

    for (size_t inlen = 0; inlen < MAX_INLEN; inlen++) {
        for (int loop = 0; loop < LOOPS; loop++) {
            // bench ref
            for (int t = 0; t < TIMINGS; t++) {
                cycles_jasmin[loop][t] = cpucycles();
                sha256_in_ptr_jazz(out, in, inlen + 1);
            }

            // bench jasmin
            for (int t = 0; t < TIMINGS; t++) {
                cycles_ref[loop][t] = cpucycles();
                SHA256(in, inlen + 1, out);
            }

            print_results(f, inlen + 1, loop, cycles_ref[loop], cycles_jasmin[loop]);
        }
    }

    if (f != NULL) {
        fclose(f);
    }

    return 0;
}