#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "params.h"

static void print_param(FILE *f, const char *name, int value) { fprintf(f, "param int %s = %d;\n", name, value); }

static void cleanup_file_path(char *filepath) {
    // Repaces / with _ and uppercase letters with lowercase
    // E.g. XMSSMT-SHAKE_60/6_512 becomes xmssmt-shake_60_6_512

    if (!filepath) {
        return;
    }

    for (size_t i = 0; i < strlen(filepath); ++i) {
        if (filepath[i] == '/') {
            filepath[i] = '_';
        } else if (filepath[i] >= 'A' && filepath[i] <= 'Z') {
            filepath[i] += ('a' - 'A');
        }
    }
}

static void print_xmss_params(const char *_impl, xmss_params *p) {
    if (!p || !_impl) {
        return;
    }

    char file_path[5000];
    char *impl;
    FILE *f;

    impl = strdup(_impl);
    cleanup_file_path(impl);
    snprintf(file_path, sizeof(file_path), "../params-%s.jinc", impl);

    f = fopen(file_path, "w");

    if (!f) {
        fprintf(stderr, "Error opening file: %s\n", file_path);
        exit(-1);
    }

    print_param(f, "XMSS_FUNC", p->func);
    print_param(f, "XMSS_N", p->n);
    print_param(f, "XMSS_PADDING_LEN", p->padding_len);
    print_param(f, "XMSS_WOTS_W", p->wots_w);
    print_param(f, "XMSS_WOTS_LOG_W", p->wots_log_w);
    print_param(f, "XMSS_WOTS_LEN1", p->wots_len1);
    print_param(f, "XMSS_WOTS_LEN2", p->wots_len2);
    print_param(f, "XMSS_WOTS_LEN", p->wots_len);
    print_param(f, "XMSS_WOTS_SIG_BYTES", p->wots_sig_bytes);
    print_param(f, "XMSS_FULL_HEIGHT", p->full_height);
    print_param(f, "XMSS_TREE_HEIGHT", p->tree_height);
    print_param(f, "XMSS_D", p->d);
    print_param(f, "XMSS_INDEX_BYTES", p->index_bytes);
    print_param(f, "XMSS_SIG_BYTES", p->sig_bytes);
    print_param(f, "XMSS_PK_BYTES", p->pk_bytes);
    print_param(f, "XMSS_SK_BYTES", p->sk_bytes);
    print_param(f, "XMSS_BDS_K", p->bds_k);

    fclose(f);
}

int main(void) {
    const char *xmss_impls[] = {"XMSS-SHA2_10_256",     "XMSS-SHA2_16_256",     "XMSS-SHA2_20_256",
                                "XMSS-SHA2_10_512",     "XMSS-SHA2_16_512",     "XMSS-SHA2_20_512",
                                "XMSS-SHAKE_10_256",    "XMSS-SHAKE_16_256",    "XMSS-SHAKE_20_256",
                                "XMSS-SHAKE_10_512",    "XMSS-SHAKE_16_512",    "XMSS-SHAKE_20_512",
                                "XMSS-SHA2_10_192",     "XMSS-SHA2_16_192",     "XMSS-SHA2_20_192",
                                "XMSS-SHAKE256_10_256", "XMSS-SHAKE256_16_256", "XMSS-SHAKE256_20_256",
                                "XMSS-SHAKE256_10_192", "XMSS-SHAKE256_16_192", "XMSS-SHAKE256_20_192"};

    const char *xmssmt_impls[] = {"XMSSMT-SHA2_20/2_256",     "XMSSMT-SHA2_20/4_256",     "XMSSMT-SHA2_40/2_256",
                                  "XMSSMT-SHA2_40/4_256",     "XMSSMT-SHA2_40/8_256",     "XMSSMT-SHA2_60/3_256",
                                  "XMSSMT-SHA2_60/6_256",     "XMSSMT-SHA2_60/12_256",    "XMSSMT-SHA2_20/2_512",
                                  "XMSSMT-SHA2_20/4_512",     "XMSSMT-SHA2_40/2_512",     "XMSSMT-SHA2_40/4_512",
                                  "XMSSMT-SHA2_40/8_512",     "XMSSMT-SHA2_60/3_512",     "XMSSMT-SHA2_60/6_512",
                                  "XMSSMT-SHA2_60/12_512",    "XMSSMT-SHAKE_20/2_256",    "XMSSMT-SHAKE_20/4_256",
                                  "XMSSMT-SHAKE_40/2_256",    "XMSSMT-SHAKE_40/4_256",    "XMSSMT-SHAKE_40/8_256",
                                  "XMSSMT-SHAKE_60/3_256",    "XMSSMT-SHAKE_60/6_256",    "XMSSMT-SHAKE_60/12_256",
                                  "XMSSMT-SHAKE_20/2_512",    "XMSSMT-SHAKE_20/4_512",    "XMSSMT-SHAKE_40/2_512",
                                  "XMSSMT-SHAKE_40/4_512",    "XMSSMT-SHAKE_40/8_512",    "XMSSMT-SHAKE_60/3_512",
                                  "XMSSMT-SHAKE_60/6_512",    "XMSSMT-SHAKE_60/12_512",   "XMSSMT-SHA2_20/2_192",
                                  "XMSSMT-SHA2_20/4_192",     "XMSSMT-SHA2_40/2_192",     "XMSSMT-SHA2_40/4_192",
                                  "XMSSMT-SHA2_40/8_192",     "XMSSMT-SHA2_60/3_192",     "XMSSMT-SHA2_60/6_192",
                                  "XMSSMT-SHA2_60/12_192",    "XMSSMT-SHAKE256_20/2_256", "XMSSMT-SHAKE256_20/4_256",
                                  "XMSSMT-SHAKE256_40/2_256", "XMSSMT-SHAKE256_40/4_256", "XMSSMT-SHAKE256_40/8_256",
                                  "XMSSMT-SHAKE256_60/3_256", "XMSSMT-SHAKE256_60/6_256", "XMSSMT-SHAKE256_60/12_256",
                                  "XMSSMT-SHAKE256_20/2_192", "XMSSMT-SHAKE256_20/4_192", "XMSSMT-SHAKE256_40/2_192",
                                  "XMSSMT-SHAKE256_40/4_192", "XMSSMT-SHAKE256_40/8_192", "XMSSMT-SHAKE256_60/3_192",
                                  "XMSSMT-SHAKE256_60/6_192", "XMSSMT-SHAKE256_60/12_192"

    };

#define XMSS_IMPLS 21
#define XMSSMT_IMPLS 56

    xmss_params p;
    uint32_t oid;

    for (int i = 0; i < XMSS_IMPLS; i++) {
        xmss_str_to_oid(&oid, xmss_impls[i]);

        if (xmss_parse_oid(&p, oid) != -1) {
            print_xmss_params(xmss_impls[i], &p);
        } else {
            fprintf(stderr, "Failed to parse oid for XMSSMT");
        }
    }

    for (int i = 0; i < XMSSMT_IMPLS; i++) {
        xmssmt_str_to_oid(&oid, xmssmt_impls[i]);

        if (xmssmt_parse_oid(&p, oid) != -1) {
            print_xmss_params(xmssmt_impls[i], &p);
        } else {
            fprintf(stderr, "Failed to parse oid for XMSSMT");
        }
    }

    return 0;
}
