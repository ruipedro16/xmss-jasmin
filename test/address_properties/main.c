#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "wots.h"

#define str(s) #s
#define xstr(s) str(s)

#ifndef IMPL
#error IMPL not defined
#endif

static int starts_with(const char *str, const char *prefix) { return strncmp(str, prefix, strlen(prefix)) == 0; }

static void print_diff_addr(const char *impl, const uint32_t *before, const uint32_t *after) {
    if (!before) {  // cannot be null
        puts("before=NULL");
        return;
    }

    if (!after) {  // cannot be null
        puts("after=NULL");
        return;
    }

    if (impl) {  // may be null
        puts("==============================================================");
        printf("[%s:]\n", impl);
    }

    for (size_t i = 0; i < 8; i++) {
        if (before[i] != after[i]) {
            printf("index %ld was changed: value = %d\n", i, after[i]);
        }
    }

    if (impl) {
        puts("==============================================================");
    }
}

int main(void) {
    uint32_t addr_before[8], addr_after[8];

    xmss_params p;
    uint32_t oid;

    if (!starts_with(xstr(IMPL), "XMSSMT")) {
        puts("THIS ONLY WORKS FOR THE MULTI TREE VARIANT");
        return -1;
    }

    if (xmssmt_str_to_oid(&oid, xstr(IMPL)) == -1) {
        fprintf(stderr, "Failed to generate oid from impl name\n");
        return -1;
    }

    if (xmssmt_parse_oid(&p, oid) == -1) {
        fprintf(stderr, "Failed to generate params from oid\n");
        return -1;
    }

    uint8_t buf0[p.n], buf1[p.n];
    uint8_t pk[p.wots_sig_bytes];

    // Expand Seed 
    // Post: addr[5] = len - 1 /\ addr[6] = 0 /\ addr[7] = 0
    memset(addr_before, -1, 8 * sizeof(uint32_t));
    memcpy(addr_after, addr_before, 8 * sizeof(uint32_t));
    assert(!memcmp(addr_before, addr_after, 8 * sizeof(uint32_t)));
    expand_seed(&p, pk, buf0, buf1, addr_after);
    print_diff_addr("expand seed", addr_before, addr_after);

    // Gen Chain inplace
    // Post: addr[6] = MIN (start + steps - 1, w - 1) /\ addr[7] = 1
    memset(addr_before, -1, 8 * sizeof(uint32_t));
    memcpy(addr_after, addr_before, 8 * sizeof(uint32_t));
    assert(!memcmp(addr_before, addr_after, 8 * sizeof(uint32_t)));
    gen_chain(&p, buf0, buf0, 0, 10, buf1, addr_after);
    print_diff_addr("gen chain inplace", addr_before, addr_after);
    return 0;
}