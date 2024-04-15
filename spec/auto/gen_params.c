#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "params.h"

#define str(s) #s
#define xstr(s) str(s)

#ifndef IMPL
#error IMPL not defined
#endif

#define MAXBUFSIZE 1024

static void print_param(FILE *f, const char *name, int value) {
    if (!f || !name) {
        return;
    }

    fprintf(f, "op %s : int = %d.\n", name, value);
}

static void print_xmss_params(xmss_params *p, uint32_t oid) {
    if (!p) {
        return;
    }

    char filename[MAXBUFSIZE];
    FILE *f;

    sprintf(filename, "../param/Parameters_%s.ec", xstr(IMPL));
    ;

    if (!(f = fopen(filename, "w"))) {
        fprintf(stderr, "Error opening file: %s\n", "../Parameters.ec");
        exit(-1);
    }

    print_param(f, "XMSS_OID_LEN", 4);

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

    fprintf(f, "\n\n");

    fclose(f);
}

int main(void) {
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

    print_xmss_params(&p, oid);

    printf("[%s]: Generated param file\n", xstr(IMPL));
    return 0;
}
