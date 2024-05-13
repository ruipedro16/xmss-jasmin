#include <inttypes.h>
#include <openssl/sha.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "cpucycles.c"
#include "macros.h"

#ifndef INLEN
#error INLEN not defined
#endif

#ifndef TIMINGS
#define TIMINGS 100
#endif

#ifndef LOOPS
#define LOOPS 10
#endif

#ifndef FILENAME
#define FILENAME "csv/bench_sha2_array.csv"
#endif

#define sha256_jazz NAMESPACE1(sha256_array, INLEN)
extern void sha256_jazz(uint8_t *, const uint8_t *);

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
    FILE *f = NULL;

    if (access(FILENAME, F_OK) == -1) {
        // if the file doesnt exist, create it
        if ((f = fopen(FILENAME, "w")) == NULL) {
            fprintf(stderr, "Failed to create file %s\n", FILENAME);
            exit(-1);
        }

        fprintf(f, "Inlen,Loop,Reference,Jasmin\n");  // Header of the csv

    } else {
        // if the file exists, we append to it (we dont want to overwrite benchmarks for other values of INLEN)
        if ((f = fopen(FILENAME, "a")) == NULL) {
            fprintf(stderr, "Failed to open file %s\n", FILENAME);
            exit(-1);
        }
    }

    uint8_t in[INLEN];
    uint8_t out[SHA256_DIGEST_LENGTH];

    uint64_t cycles_ref[LOOPS][TIMINGS];
    uint64_t cycles_jasmin[LOOPS][TIMINGS];

    // warmup
    for (int t = 0; t < TIMINGS; t++) {
        sha256_jazz(out, in);
        SHA256(in, 42, out);
    }

    for (int loop = 0; loop < LOOPS; loop++) {
        // bench ref
        for (int t = 0; t < TIMINGS; t++) {
            cycles_jasmin[loop][t] = cpucycles();
            sha256_jazz(out, in);
        }

        // bench jasmin
        for (int t = 0; t < TIMINGS; t++) {
            cycles_ref[loop][t] = cpucycles();
            SHA256(in, INLEN, out);
        }

        print_results(f, INLEN, loop, cycles_ref[loop], cycles_jasmin[loop]);
    }

    if (f != NULL) {
        fclose(f);
    }

    return 0;
}