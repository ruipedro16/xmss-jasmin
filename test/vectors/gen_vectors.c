#include <assert.h>
#include <inttypes.h>
#include <math.h>
#include <pthread.h>
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

// 2500 / 4 = 625

#ifndef N
#define N 625
#endif

typedef struct {
    int thread_id;
    int num_threads;
    bool debug;
} thread_params;

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

void *vectors_xmss(void *args) {
    thread_params *p = (thread_params *)args;

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
            fprintf(stderr, "Thread %d: %d/%d\n", p->thread_id, i + 1, N);
        }

        randombytes((uint8_t *)seed, params.n * 3);

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

    return NULL;
}

int main(void) {
    int num_threads = 4;
    pthread_t threads[num_threads];
    thread_params params[num_threads];

    for (int i = 0; i < num_threads; i++) {
        params[i].thread_id = i;
        params[i].num_threads = num_threads;
        params[i].debug = true;

        int rc = pthread_create(&threads[i], NULL, vectors_xmss, (void *)&params[i]);
        if (rc) {
            fprintf(stderr, "Error: Unable to create thread %d\n", rc);
            exit(-1);
        }
    }

    for (int i = 0; i < num_threads; i++) {
        pthread_join(threads[i], NULL);
    }

    return 0;
}