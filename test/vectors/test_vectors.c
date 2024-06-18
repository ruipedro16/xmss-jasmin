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

#ifndef N
#define N 500
#endif

extern int xmssmt_core_seed_keypair_jazz(uint8_t *pk, uint8_t *sk, const uint8_t *seed);
extern int xmssmt_core_sign_jazz(unsigned char *sk, unsigned char *sm, unsigned long long *smlen,
                                 const unsigned char *m, unsigned long long mlen);

static int starts_with(const char *str, const char *prefix) { return strncmp(str, prefix, strlen(prefix)) == 0; }

static int cmp_files(const char *filePath1, const char *filePath2) {
    if (!filePath1 || !filePath2) {
        return -1;
    }

    FILE *file1 = fopen(filePath1, "rb");
    FILE *file2 = fopen(filePath2, "rb");

    if (file1 == NULL || file2 == NULL) {
        if (file1 != NULL) fclose(file1);
        if (file2 != NULL) fclose(file2);
        perror("Error opening file");
        return 0;  // Indicate files are not equal (couldn't open one or both files)
    }

    int result = 1;  // Assume files are equal initially
    int byte1, byte2;

    while ((byte1 = fgetc(file1)) != EOF && (byte2 = fgetc(file2)) != EOF) {
        if (byte1 != byte2) {
            result = 0;
            break;
        }
    }

    // Check if both files have reached the end
    if ((byte1 != EOF || byte2 != EOF) && result == 1) {
        result = 0;
    }

    fclose(file1);
    fclose(file2);
    return result;
}

void fprint_hex(FILE *f, unsigned char *buf, int len) {
    for (int i = 0; i < len; i++) {
        fprintf(f, "%x%x", buf[i] / 16, buf[i] & 15);
    }
}

void fprint_hash(FILE *f, unsigned char *buf, int len) {
    unsigned char tmp[10];
    shake128(tmp, 10, buf, len);
    fprint_hex(f, tmp, 10);
}

int main(void) {
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

    FILE *f = NULL;
    f = fopen("vectors/tmp.txt", "w");

    for (int i = 0; i < N; i++) {
        if (debug) {
            printf("%d/%d\n", i + 1, N);
        }

        randombytes((uint8_t *)seed, params.n * 3);

        xmssmt_core_seed_keypair_jazz(pk, sk, seed);

        ull_to_bytes(sk, params.index_bytes, 1 << (params.full_height - 1));

        xmssmt_core_sign_jazz(sk, sm, &smlen, msg, 1);

        if (mt) {
            fprintf(f, "XMSSMT ");
        } else {
            fprintf(f, "XMSS ");
        }

        fprintf(f, "%d ", oid);
        fprintf(f, " ");
        fprint_hash(f, seed, 3 * params.n);
        fprintf(f, " ");
        fprint_hash(f, pk, params.pk_bytes);
        fprintf(f, " ");
        fprint_hash(f, sm, params.sig_bytes);
        fprintf(f, "\n");
    }

    fclose(f);

    assert(cmp_files("vectors/vectors.txt", "vectors/vectors_tmp.txt"));

    remove("vectors/tmp.txt");  // only delete the file if all vectors are ok

    return 0;
}