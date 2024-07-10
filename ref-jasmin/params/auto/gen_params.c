#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "params.h"

/*
 * Given a set of parameters, this function returns the size of the secret key.
 * This is implementation specific, as varying choices in tree traversal will
 * result in varying requirements for state storage.
 *
 * This function handles both XMSS and XMSSMT parameter sets.
 */
unsigned long long xmss_fast_core_sk_bytes(const xmss_params *params) {
    return params->index_bytes + 4 * params->n +
           (2 * params->d - 1) *
               ((params->tree_height + 1) * params->n + 4 + params->tree_height + 1 + params->tree_height * params->n +
                (params->tree_height >> 1) * params->n + (params->tree_height - params->bds_k) * (7 + params->n) +
                ((1 << params->bds_k) - params->bds_k - 1) * params->n + 4) +
           (params->d - 1) * params->wots_sig_bytes;
}

#ifdef DEBUG
static int starts_with(const char *str, const char *prefix) { return strncmp(str, prefix, strlen(prefix)) == 0; }

static void debug_print(const char *impl) {
    if (!p) {
        return;
    }

    xmss_params p;
    uint32_t oid;

    if (starts_with(impl, "XMSSMT")) {
        if (xmssmt_str_to_oid(&oid, impl) == -1) {
            fprintf(stderr, "Failed to get oid from str\n");
            exit(-1);
        }

        if (xmssmt_parse_oid(&p, oid) == -1) {
            fprintf(stderr, "Failed to get params from oid\n");
            exit(-1);
        }

    } else {
        if (xmss_str_to_oid(&oid, impl) == -1) {
            fprintf(stderr, "Failed to get oid from str\n");
            exit(-1);
        }

        if (xmss_parse_oid(&p, oid) == -1) {
            fprintf(stderr, "Failed to get params from oid\n");
            exit(-1);
        }
    }
}
#endif

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

static void print_xmss_params(const char *_impl, xmss_params *p, uint32_t oid) {
    if (!p || !_impl) {
        return;
    }

    char file_path[5000];
    char *impl;
    FILE *f;

    impl = strdup(_impl);
    cleanup_file_path(impl);
    snprintf(file_path, sizeof(file_path), "../params-%s.jinc", impl);

    if (!(f = fopen(file_path, "w"))) {
        fprintf(stderr, "Error opening file: %s\n", file_path);
        exit(-1);
    }

    print_param(f, "XMSS_OID_LEN", 4);

    print_param(f, "XMSS_SHA2", 0);
    print_param(f, "XMSS_SHAKE128", 1);
    print_param(f, "XMSS_SHAKE256", 2);

    print_param(f, "XMSS_ADDR_TYPE_OTS", 0);
    print_param(f, "XMSS_ADDR_TYPE_LTREE", 1);
    print_param(f, "XMSS_ADDR_TYPE_HASHTREE", 2);

    print_param(f, "XMSS_HASH_PADDING_F", 0);
    print_param(f, "XMSS_HASH_PADDING_H", 1);
    print_param(f, "XMSS_HASH_PADDING_HASH", 2);
    print_param(f, "XMSS_HASH_PADDING_PRF", 3);
    print_param(f, "XMSS_HASH_PADDING_PRF_KEYGEN", 4);

    print_param(f, "XMSS_OID", oid);
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

    // FAST
    print_param(f, "XMSS_BDS_K", p->bds_k);
    print_param(f, "XMSS_FAST_SK_BYTES", xmss_fast_core_sk_bytes(p));

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
            print_xmss_params(xmss_impls[i], &p, oid);

#ifdef DEBUG
            debug_print(xmss_impls[i]);
#endif
        } else {
            fprintf(stderr, "Failed to parse oid for XMSS");
        }
    }

    for (int i = 0; i < XMSSMT_IMPLS; i++) {
        xmssmt_str_to_oid(&oid, xmssmt_impls[i]);

        if (xmssmt_parse_oid(&p, oid) != -1) {
            print_xmss_params(xmssmt_impls[i], &p, oid);

#ifdef DEBUG
            debug_print(xmssmt_impls[i]);
#endif
        } else {
            fprintf(stderr, "Failed to parse oid for XMSSMT");
        }
    }

    puts("Generated param files");
    return 0;
}
