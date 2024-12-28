#include <assert.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "params.h"
#include "xmss.h"

#ifndef DATA_POINTS
#define DATA_POINTS 100000
#endif

#ifndef IMPL
#define IMPL "XMSSMT-SHA2_20/2_256"
#endif

#ifndef XMSSMT_KG_FILE
#define XMSSMT_KG_FILE "csv/xmssmt_kg.csv"
#endif

#ifndef XMSS_KG_FILE
#define XMSS_KG_FILE "csv/xmss_kg.csv"
#endif

#ifndef XMSSMT_SIGN_FILE
#define XMSSMT_SIGN_FILE "csv/xmssmt_sign.csv"
#endif

#ifndef XMSS_SIGN_FILE
#define XMSS_SIGN_FILE "csv/xmss_sign.csv"
#endif

#ifndef MESSAGE_SIZE
#define MESSAGE_SIZE 65
#endif

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Based on
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

extern int xmss_keypair_jazz(uint8_t *pk, uint8_t *sk);
extern int xmss_sign_jazz(uint8_t *sk, uint8_t *sm, size_t *smlen, const uint8_t *m, size_t mlen);
extern int xmss_sign_open_jazz(uint8_t *m, size_t *mlen, const uint8_t *sm, size_t smlen, const uint8_t *pk);

extern int xmssmt_keypair_jazz(uint8_t *pk, uint8_t *sk);
extern int xmssmt_sign_jazz(uint8_t *sk, uint8_t *sm, size_t *smlen, const uint8_t *m, size_t mlen);
extern int xmssmt_sign_open_jazz(uint8_t *m, size_t *mlen, const uint8_t *sm, size_t smlen, const uint8_t *pk);

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

static int starts_with(const char *str, const char *prefix) { return strncmp(str, prefix, strlen(prefix)) == 0; }

bool file_exists(const char *filename) {
    assert(filename != NULL);

    FILE *file = fopen(filename, "r");

    if (file != NULL) {
        fclose(file);
        return true;
    }
    return false;
}

void write_csv_header(const char *filename, const char *op) {
    assert(filename != NULL);
    assert(op != NULL);

    FILE *file = fopen(filename, "w");

    if (file == NULL) {
        perror("Failed to open file");
        exit(EXIT_FAILURE);
    }

    fprintf(file, "op;median_ref;avg_ref;median_jasmin;avg_jasmin\n");
    fclose(file);
}

void write_results(const char *filename, const char *op, uint64_t median_ref, uint64_t avg_ref, uint64_t median_jasmin,
                   uint64_t avg_jasmin) {
    assert(filename != NULL);
    assert(op != NULL);

    FILE *file = fopen(filename, "a");
    if (file == NULL) {
        perror("Failed to open file");
        exit(EXIT_FAILURE);
    }

    fprintf(file, "%s;%" PRIu64 ";%" PRIu64 ";%" PRIu64 ";%" PRIu64 "\n", op, median_ref, avg_ref, median_jasmin,
            avg_jasmin);
    fclose(file);
}

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

static inline uint64_t cpucycles(void) {
    uint64_t result;

    asm volatile("rdtsc; shlq $32,%%rdx; orq %%rdx,%%rax" : "=a"(result) : : "%rdx");

    return result;
}

static int cmp_uint64(const void *a, const void *b) {
    if (*(uint64_t *)a < *(uint64_t *)b) {
        return -1;
    }
    if (*(uint64_t *)a > *(uint64_t *)b) {
        return 1;
    }
    return 0;
}

static uint64_t median(uint64_t *l, size_t llen) {
    qsort(l, llen, sizeof(uint64_t), cmp_uint64);

    if (llen % 2) {
        return l[llen / 2];
    } else {
        return (l[llen / 2 - 1] + l[llen / 2]) / 2;
    }
}

static uint64_t average(uint64_t *t, size_t tlen) {
    size_t i;
    uint64_t acc = 0;

    for (i = 0; i < tlen; i++) {
        acc += t[i];
    }

    return acc / tlen;
}

static uint64_t overhead_of_cpucycles_call(void) {
    uint64_t t0, t1, overhead = -1LL;
    unsigned int i;

    for (i = 0; i < 100000; i++) {
        t0 = cpucycles();
        __asm__ volatile("");
        t1 = cpucycles();
        if (t1 - t0 < overhead) {
            overhead = t1 - t0;
        }
    }

    return overhead;
}

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

void xmssmt_bench_kg(const xmss_params *params, uint32_t oid) {
    assert(params != NULL);

    uint8_t pk_ref[XMSS_OID_LEN + params->pk_bytes];
    uint8_t sk_ref[XMSS_OID_LEN + params->sk_bytes];
    uint8_t pk_jasmin[XMSS_OID_LEN + params->pk_bytes];
    uint8_t sk_jasmin[XMSS_OID_LEN + params->sk_bytes];

    uint64_t observations_ref[DATA_POINTS];
    uint64_t observations_jasmin[DATA_POINTS];

    uint64_t before, after;

    uint64_t cpucycles_overhead = overhead_of_cpucycles_call();

    if (!file_exists(XMSSMT_KG_FILE)) {
        write_csv_header(XMSSMT_KG_FILE, "xmssmt_keypair");
    }

    for (size_t i = 0; i + 1 < DATA_POINTS; i++) {
        before = cpucycles();
        xmssmt_keypair(pk_ref, sk_ref, oid);
        after = cpucycles();
        observations_ref[i] = (after - cpucycles_overhead) - before;

        before = cpucycles();
        xmssmt_keypair_jazz(pk_jasmin, sk_jasmin);
        after = cpucycles();
        observations_jasmin[i] = (after - cpucycles_overhead) - before;
    }

    uint64_t median_ref = median(observations_ref, DATA_POINTS);
    uint64_t median_jasmin = median(observations_jasmin, DATA_POINTS);
    uint64_t avg_ref = average(observations_ref, DATA_POINTS);
    uint64_t avg_jasmin = average(observations_jasmin, DATA_POINTS);
    write_results(XMSSMT_KG_FILE, "xmssmt_keypair", median_ref, avg_ref, median_jasmin, avg_jasmin);
}

void xmss_bench_kg(const xmss_params *params, uint32_t oid) {
    assert(params != NULL);

    uint8_t pk_ref[XMSS_OID_LEN + params->pk_bytes];
    uint8_t sk_ref[XMSS_OID_LEN + params->sk_bytes];
    uint8_t pk_jasmin[XMSS_OID_LEN + params->pk_bytes];
    uint8_t sk_jasmin[XMSS_OID_LEN + params->sk_bytes];

    uint64_t observations_ref[DATA_POINTS];
    uint64_t observations_jasmin[DATA_POINTS];

    uint64_t before, after;

    uint64_t cpucycles_overhead = overhead_of_cpucycles_call();

    if (!file_exists(XMSS_KG_FILE)) {
        write_csv_header(XMSS_KG_FILE, "xmss_keypair");
    }

    for (size_t i = 0; i + 1 < DATA_POINTS; i++) {
        before = cpucycles();
        xmss_keypair(pk_ref, sk_ref, oid);
        after = cpucycles();
        observations_ref[i] = (after - cpucycles_overhead) - before;

        before = cpucycles();
        xmss_keypair_jazz(pk_jasmin, sk_jasmin);
        after = cpucycles();
        observations_jasmin[i] = (after - cpucycles_overhead) - before;
    }

    uint64_t median_ref = median(observations_ref, DATA_POINTS);
    uint64_t median_jasmin = median(observations_jasmin, DATA_POINTS);
    uint64_t avg_ref = average(observations_ref, DATA_POINTS);
    uint64_t avg_jasmin = average(observations_jasmin, DATA_POINTS);
    write_results(XMSS_KG_FILE, "xmss_keypair", median_ref, avg_ref, median_jasmin, avg_jasmin);
}

void xmssmt_bench_sign(const xmss_params *params, uint32_t oid) {
    assert(params != NULL);

    uint8_t m[MESSAGE_SIZE];
    uint8_t pk[XMSS_OID_LEN + params->pk_bytes];
    uint8_t sk_ref[XMSS_OID_LEN + params->sk_bytes];
    uint8_t sk_jasmin[XMSS_OID_LEN + params->sk_bytes];
    uint8_t sm_ref[params->sig_bytes + MESSAGE_SIZE];
    uint8_t sm_jasmin[params->sig_bytes + MESSAGE_SIZE];
    size_t smlen_ref, smlen_jasmin;

    uint64_t observations_ref[DATA_POINTS];
    uint64_t observations_jasmin[DATA_POINTS];

    uint64_t before, after;

    uint64_t cpucycles_overhead = overhead_of_cpucycles_call();

    if (!file_exists(XMSSMT_SIGN_FILE)) {
        write_csv_header(XMSSMT_SIGN_FILE, "xmssmt_sign");
    }

    // First we need to generate a keypair
    xmssmt_keypair(pk, sk_ref, oid);
    memcpy(sk_jasmin, sk_ref, XMSS_OID_LEN + params->sk_bytes);

    for (size_t i = 0; i + 1 < DATA_POINTS; i++) {
        before = cpucycles();
        xmssmt_sign(sk_ref, sm_ref, (unsigned long long *)&smlen_ref, m, MESSAGE_SIZE);
        after = cpucycles();
        observations_ref[i] = (after - cpucycles_overhead) - before;

        before = cpucycles();
        xmssmt_sign_jazz(sk_jasmin, sm_jasmin, &smlen_jasmin, m, MESSAGE_SIZE);
        after = cpucycles();
        observations_jasmin[i] = (after - cpucycles_overhead) - before;
    }

    uint64_t median_ref = median(observations_ref, DATA_POINTS);
    uint64_t median_jasmin = median(observations_jasmin, DATA_POINTS);
    uint64_t avg_ref = average(observations_ref, DATA_POINTS);
    uint64_t avg_jasmin = average(observations_jasmin, DATA_POINTS);
    write_results(XMSSMT_SIGN_FILE, "xmssmt_sign", median_ref, avg_ref, median_jasmin, avg_jasmin);
}

void xmss_bench_sign(const xmss_params *params, uint32_t oid) {
    assert(params != NULL);

    uint8_t m[MESSAGE_SIZE];
    uint8_t pk[XMSS_OID_LEN + params->pk_bytes];
    uint8_t sk_ref[XMSS_OID_LEN + params->sk_bytes];
    uint8_t sk_jasmin[XMSS_OID_LEN + params->sk_bytes];
    uint8_t sm_ref[params->sig_bytes + MESSAGE_SIZE];
    uint8_t sm_jasmin[params->sig_bytes + MESSAGE_SIZE];
    size_t smlen_ref, smlen_jasmin;

    uint64_t observations_ref[DATA_POINTS];
    uint64_t observations_jasmin[DATA_POINTS];

    uint64_t before, after;

    uint64_t cpucycles_overhead = overhead_of_cpucycles_call();

    if (!file_exists(XMSS_SIGN_FILE)) {
        write_csv_header(XMSS_SIGN_FILE, "xmss_sign");
    }

    // First we need to generate a keypair
    xmss_keypair(pk, sk_ref, oid);
    memcpy(sk_jasmin, sk_ref, XMSS_OID_LEN + params->sk_bytes);

    for (size_t i = 0; i + 1 < DATA_POINTS; i++) {
        before = cpucycles();
        xmss_sign(sk_ref, sm_ref, (unsigned long long *)&smlen_ref, m, MESSAGE_SIZE);
        after = cpucycles();
        observations_ref[i] = (after - cpucycles_overhead) - before;

        before = cpucycles();
        xmss_sign_jazz(sk_jasmin, sm_jasmin, &smlen_jasmin, m, MESSAGE_SIZE);
        after = cpucycles();
        observations_jasmin[i] = (after - cpucycles_overhead) - before;
    }

    uint64_t median_ref = median(observations_ref, DATA_POINTS);
    uint64_t median_jasmin = median(observations_jasmin, DATA_POINTS);
    uint64_t avg_ref = average(observations_ref, DATA_POINTS);
    uint64_t avg_jasmin = average(observations_jasmin, DATA_POINTS);
    write_results(XMSS_SIGN_FILE, "xmss_sign", median_ref, avg_ref, median_jasmin, avg_jasmin);
}

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

int main(void) {
    xmss_params params;
    uint32_t oid;

    if (starts_with(IMPL, "XMSSMT")) {
        if (xmssmt_str_to_oid(&oid, IMPL) == -1) {
            fprintf(stderr, "Failed to generate oid from impl name\n");
            exit(-1);
        }

        if (xmssmt_parse_oid(&params, oid) == -1) {
            fprintf(stderr, "Failed to generate params from oid\n");
            exit(-1);
        }

        xmssmt_bench_kg(&params, oid);
        xmssmt_bench_sign(&params, oid);

    } else {
        if (xmss_str_to_oid(&oid, IMPL) == -1) {
            fprintf(stderr, "Failed to generate oid from impl name\n");
            exit(-1);
        }

        if (xmss_parse_oid(&params, oid) == -1) {
            fprintf(stderr, "Failed to generate params from oid\n");
            exit(-1);
        }

        xmss_bench_kg(&params, oid);
        xmss_bench_sign(&params, oid);
    }

    return EXIT_SUCCESS;
}