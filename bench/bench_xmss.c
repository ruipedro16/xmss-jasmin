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

#ifndef MIN_MSG_LEN
#define MIN_MSG_LEN 1
#endif

#ifndef TIMINGS
#define TIMINGS 10000
#endif

#ifndef LOOPS
#define LOOPS 10
#endif

#define MAX_BUF_SIZE 2048

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

extern int xmss_keypair_jazz(uint8_t *pk, uint8_t *sk);
extern int xmssmt_keypair_jazz(uint8_t *pk, uint8_t *sk);

extern int xmss_sign_jazz(uint8_t *sk, uint8_t *sm, size_t *smlen, const uint8_t *m, size_t mlen);
extern int xmssmt_sign_jazz(uint8_t *sk, uint8_t *sm, size_t *smlen, const uint8_t *m, size_t mlen);

extern int xmss_sign_open_jazz(uint8_t *m, size_t *mlen, const uint8_t *sm, size_t smlen, const uint8_t *pk);
extern int xmssmt_sign_open_jazz(uint8_t *m, size_t *mlen, const uint8_t *sm, size_t smlen, const uint8_t *pk);

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

static int starts_with(const char *str, const char *prefix) { return strncmp(str, prefix, strlen(prefix)) == 0; }

static void print_results(FILE *f, int loop, size_t message_len, const char *operation, uint64_t cycles_ref[TIMINGS],
                          uint64_t cycles_jasmin[TIMINGS]) {
    if (!f) {
        fprintf(stderr, "FILE *f is NULL in print_results\n");
        exit(-1);
    }

    if (!operation) {
        fprintf(stderr, "char* operation is NULL in print_results\n");
    }

    cpucycles_median(cycles_ref, TIMINGS);
    cpucycles_median(cycles_jasmin, TIMINGS);

    for (size_t i = 0; i < TIMINGS - 1; i++) {
        fprintf(f, "%d,%s,%ld,%ld,%ld\n", loop, operation, message_len, cycles_ref[i], cycles_jasmin[i]);
    }

}

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

void bench_xmss(void) {
    bool verbose = true;
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

    char filename[MAX_BUF_SIZE] = {0};

    sprintf(filename, "csv/bench_%s.csv", xstr(IMPL));

    FILE *f;
    if ((f = fopen(filename, "w")) == NULL) {
        fprintf(stderr, "Failed to open file %s\n", filename);
        exit(-1);
    }

    fprintf(f, "Loop,Operation,MessageLen,Reference,Jasmin\n");  // Header of the CSV

    uint8_t m[MAX_MSG_LEN];
    uint8_t pk[XMSS_OID_LEN + p.pk_bytes];
    uint8_t sk[XMSS_OID_LEN + p.sk_bytes];
    uint8_t sm[p.sig_bytes + MAX_MSG_LEN];
    size_t mlen, smlen;

    uint64_t cycles_ref[LOOPS][TIMINGS], cycles_jasmin[LOOPS][TIMINGS];

    // Warmup
    for (int i = 0; i < 10; i++) {
        xmss_keypair_jazz(pk, sk);
        xmss_sign_jazz(sk, sm, &smlen, m, MAX_MSG_LEN);
        xmss_sign_open_jazz(m, &mlen, sm, smlen, pk);
    }

    for (int loop = 0; loop < LOOPS; loop++) {
        // Keypair [ref]
        for (int i = 0; i < TIMINGS; i++) {
            cycles_ref[loop][i] = cpucycles();
            xmss_keypair(pk, sk, oid);
        }

        // Keypair [jasmin]
        for (int i = 0; i < TIMINGS; i++) {
            cycles_jasmin[loop][i] = cpucycles();
            xmss_keypair_jazz(pk, sk);
        }

        if (verbose) {
            puts("Finished keypair");
        }

        print_results(f, loop, -1, "keypair", cycles_ref[loop], cycles_jasmin[loop]);

        for (size_t message_len = MIN_MSG_LEN; message_len <= MAX_MSG_LEN; message_len++) {
            if (verbose) {
                printf("[MessageLen=%ld]: Loop iteration: %d\n", message_len, loop);
            }

            // Sign [ref]
            for (int i = 0; i < TIMINGS; i++) {
                cycles_ref[loop][i] = cpucycles();
                xmss_sign(sk, sm, &smlen, m, message_len);
            }

            // Sign [jasmin]
            for (int i = 0; i < TIMINGS; i++) {
                cycles_jasmin[loop][i] = cpucycles();
                xmss_sign_jazz(sk, sm, &smlen, m, message_len);
            }

            if (verbose) {
                puts("Finished sign");
            }

            print_results(f, loop, message_len, "sign", cycles_ref[loop], cycles_jasmin[loop]);

            // Sign Open [ref]
            for (int i = 0; i < TIMINGS; i++) {
                cycles_ref[loop][i] = cpucycles();
                xmss_sign_open(m, (unsigned long long *)&mlen, sm, smlen, pk);
            }

            // Sign Open [jasmin]
            for (int i = 0; i < TIMINGS; i++) {
                cycles_jasmin[loop][i] = cpucycles();
                xmss_sign_open_jazz(m, &mlen, sm, smlen, pk);
            }

            if (verbose) {
                puts("Finished sign open");
            }

            print_results(f, loop, message_len, "sign_open", cycles_ref[loop], cycles_jasmin[loop]);
        }
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

void bench_xmssmt(void) {
    bool verbose = true;
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

    char filename[MAX_BUF_SIZE] = {0};

#ifdef ALL_TIMINGS
    sprintf(filename, "csv/bench_%s_all_timings.csv", xstr(IMPL));
#else
    sprintf(filename, "csv/bench_%s.csv", xstr(IMPL));
#endif

    FILE *f;
    if ((f = fopen(filename, "w")) == NULL) {
        fprintf(stderr, "Failed to open file csv/bench_xmssmt.csv\n");
        exit(-1);
    }

    fprintf(f, "Loop,Operation,MessageLen,Reference,Jasmin\n");  // Header of the CSV

    uint8_t m[MAX_MSG_LEN];
    uint8_t pk[XMSS_OID_LEN + p.pk_bytes];
    uint8_t sk[XMSS_OID_LEN + p.sk_bytes];
    uint8_t sm[p.sig_bytes + MAX_MSG_LEN];
    size_t mlen, smlen;

    uint64_t cycles_ref[LOOPS][TIMINGS], cycles_jasmin[LOOPS][TIMINGS];

    // Warmup
    for (int i = 0; i < 10; i++) {
        xmssmt_keypair_jazz(pk, sk);
        xmssmt_sign_jazz(sk, sm, &smlen, m, MAX_MSG_LEN);
        xmssmt_sign_open_jazz(m, &mlen, sm, smlen, pk);
    }

    for (int loop = 0; loop < LOOPS; loop++) {
        // Keypair [ref]
        for (int i = 0; i < TIMINGS; i++) {
            cycles_ref[loop][i] = cpucycles();
            xmssmt_keypair(pk, sk, oid);
        }

        // Keypair [jasmin]
        for (int i = 0; i < TIMINGS; i++) {
            cycles_jasmin[loop][i] = cpucycles();
            xmssmt_keypair_jazz(pk, sk);
        }

        if (verbose) {
            puts("Finished keypair");
        }

        print_results(f, loop, -1, "keypair", cycles_ref[loop], cycles_jasmin[loop]);

        for (size_t message_len = 1; message_len <= MAX_MSG_LEN; message_len++) {
            if (verbose) {
                printf("[MessageLen=%ld]: Loop iteration: %d\n", message_len, loop);
            }

            // Sign [ref]
            for (int i = 0; i < TIMINGS; i++) {
                cycles_ref[loop][i] = cpucycles();
                xmssmt_sign(sk, sm, &smlen, m, message_len);
            }

            // Sign [jasmin]
            for (int i = 0; i < TIMINGS; i++) {
                cycles_jasmin[loop][i] = cpucycles();
                xmssmt_sign_jazz(sk, sm, &smlen, m, message_len);
            }

            if (verbose) {
                puts("Finished sign");
            }

            print_results(f, loop, message_len, "sign", cycles_ref[loop], cycles_jasmin[loop]);

            // Sign Open [ref]
            for (int i = 0; i < TIMINGS; i++) {
                cycles_ref[loop][i] = cpucycles();
                xmssmt_sign_open(m, (unsigned long long *)&mlen, sm, smlen, pk);
            }

            // Sign Open [jasmin]
            for (int i = 0; i < TIMINGS; i++) {
                cycles_jasmin[loop][i] = cpucycles();
                xmssmt_sign_open_jazz(m, &mlen, sm, smlen, pk);
            }

            if (verbose) {
                puts("Finished sign open");
            }

            print_results(f, loop, message_len, "sign_open", cycles_ref[loop], cycles_jasmin[loop]);
        }
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

int main(void) {
    starts_with(xstr(IMPL), "XMSSMT") ? bench_xmssmt() : bench_xmss();
    printf("Finished running benchmarks for %s\n", xstr(IMPL));
    return 0;
}
