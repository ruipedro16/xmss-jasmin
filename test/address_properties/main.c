#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "hash.h"
#include "randombytes.h"
#include "wots.h"
#include "xmss_commons.h"

#define str(s) #s
#define xstr(s) str(s)

#ifndef IMPL
#error IMPL not defined
#endif

static int starts_with(const char *str, const char *prefix) { return strncmp(str, prefix, strlen(prefix)) == 0; }

static void flip_addr(uint32_t *a, size_t idx) {
    assert(a != NULL);
    assert(idx < 8);

    a[idx] ^= 0xFFFFFFFF;
}

static void print_diff_addr(const char *impl, const uint32_t *before, const uint32_t *after) {
    assert(impl != NULL);
    assert(before != NULL);
    assert(after != NULL);

    for (size_t i = 0; i < 8; i++) {
        if (before[i] != after[i]) {
            printf("[%s:] index %ld was changed: value = %d\n", impl, i, after[i]);
        }
    }
}

void test_pre_wots_pk_gen(const xmss_params *p) {
    assert(p != NULL);

    uint8_t pub_seed[p->n], sk_seed[p->n];
    uint8_t pk0[p->wots_sig_bytes], pk1[p->wots_sig_bytes];
    uint32_t addr0[8], addr1[8];

    randombytes(pub_seed, p->n * sizeof(uint8_t));
    randombytes(sk_seed, p->n * sizeof(uint8_t));

    for (size_t i = 0; i < 8; i++) {
        memset(pk0, 0, p->wots_sig_bytes);
        memset(pk1, 0, p->wots_sig_bytes);

        randombytes((uint8_t *)addr0, 8 * sizeof(uint32_t));
        memcpy(addr1, addr0, 8 * sizeof(uint32_t));

        assert(!memcmp(addr0, addr1, 8 * sizeof(uint32_t)));

        flip_addr(addr1, i);

        assert(addr0[i] != addr1[i]);

        for (size_t j = 0; j < 8; j++) {
            if (j != i) {
                assert(addr0[j] == addr1[j]);
            }
        }

        wots_pkgen(p, pk0, sk_seed, pub_seed, addr0);
        wots_pkgen(p, pk1, sk_seed, pub_seed, addr1);

        if (!memcmp(pk0, pk1, p->wots_sig_bytes) && true) {
            printf("[wots_pkgen]: Changing index %ld of the address does not change the result\n", i);
        }

        if (memcmp(pk0, pk1, p->wots_sig_bytes) && false) {
            printf("[wots_pkgen]: Changing index %ld of the address changes the result\n", i);
        }
    }
}

void test_pre_expand_seed(const xmss_params *p) {
    assert(p != NULL);

    uint8_t pub_seed[p->n], sk_seed[p->n];
    uint8_t pk0[p->wots_sig_bytes], pk1[p->wots_sig_bytes];
    uint32_t addr0[8], addr1[8];

    randombytes(pub_seed, p->n * sizeof(uint8_t));
    randombytes(sk_seed, p->n * sizeof(uint8_t));

    for (size_t i = 0; i < 8; i++) {
        memset(pk0, 0, p->wots_sig_bytes);
        memset(pk1, 0, p->wots_sig_bytes);

        randombytes((uint8_t *)addr0, 8 * sizeof(uint32_t));
        memcpy(addr1, addr0, 8 * sizeof(uint32_t));

        assert(!memcmp(addr0, addr1, 8 * sizeof(uint32_t)));

        flip_addr(addr1, i);

        assert(addr0[i] != addr1[i]);

        for (size_t j = 0; j < 8; j++) {
            if (j != i) {
                assert(addr0[j] == addr1[j]);
            }
        }

        expand_seed(p, pk0, sk_seed, pub_seed, addr0);
        expand_seed(p, pk1, sk_seed, pub_seed, addr1);

        if (!memcmp(pk0, pk1, p->wots_sig_bytes) && true) {
            printf("[expand_seed]: Changing index %ld of the address does not change the result\n", i);
        }

        if (memcmp(pk0, pk1, p->wots_sig_bytes) && false) {
            printf("[expand_seed]: Changing index %ld of the address changes the result\n", i);
        }
    }
}

void test_pre_gen_chain_inplace(const xmss_params *p) {
    assert(p != NULL);

    uint8_t pub_seed[p->n], sk_seed[p->n];
    uint8_t buf0[p->n], buf1[p->n];
    uint32_t addr0[8], addr1[8];
    uint32_t start, steps;

    do {
        randombytes((uint8_t *)&start, sizeof(uint32_t));
        randombytes((uint8_t *)&steps, sizeof(uint32_t));
    } while (start + steps >= p->wots_w);

    if (start > steps) {
        uint32_t temp = start;
        start = steps;
        steps = temp;
    }

    assert(start + steps <= p->wots_w - 1);

    randombytes(pub_seed, p->n * sizeof(uint8_t));
    randombytes(sk_seed, p->n * sizeof(uint8_t));

    for (size_t i = 0; i < 8; i++) {
        randombytes(buf0, p->n);
        randombytes(buf1, p->n);

        randombytes((uint8_t *)addr0, 8 * sizeof(uint32_t));
        memcpy(addr1, addr0, 8 * sizeof(uint32_t));

        assert(!memcmp(addr0, addr1, 8 * sizeof(uint32_t)));

        flip_addr(addr1, i);

        assert(addr0[i] != addr1[i]);

        for (size_t j = 0; j < 8; j++) {
            if (j != i) {
                assert(addr0[j] == addr1[j]);
            }
        }

        gen_chain(p, buf0, buf0, start, steps, pub_seed, addr0);
        gen_chain(p, buf1, buf1, start, steps, pub_seed, addr1);

        if (!memcmp(buf0, buf1, p->n) && true) {
            printf("[gen_chain]: Changing index %ld of the address does not change the result\n", i);
        }

        if (memcmp(buf0, buf1, p->n) && true) {
            printf("[gen_chain]: Changing index %ld of the address changes the result\n", i);
        }
    }
}

void test_pre_ltree(const xmss_params *p) {
    assert(p != NULL);

    uint8_t pub_seed[p->n];
    uint8_t leaf0[p->n], leaf1[p->n];
    uint8_t wots_pk0[p->wots_sig_bytes], wots_pk1[p->wots_sig_bytes];
    uint32_t addr0[8], addr1[8];

    randombytes(pub_seed, p->n * sizeof(uint8_t));

    for (size_t i = 0; i < 8; i++) {
        memset(leaf0, -1, p->n);
        memset(leaf1, -1, p->n);

        randombytes(wots_pk0, p->wots_sig_bytes);
        memcpy(wots_pk1, wots_pk0, p->wots_sig_bytes);
        assert(!memcmp(wots_pk0, wots_pk1, p->wots_sig_bytes));

        randombytes((uint8_t *)addr0, 8 * sizeof(uint32_t));
        memcpy(addr1, addr0, 8 * sizeof(uint32_t));

        assert(!memcmp(addr0, addr1, 8 * sizeof(uint32_t)));

        flip_addr(addr1, i);

        assert(addr0[i] != addr1[i]);

        for (size_t j = 0; j < 8; j++) {
            if (j != i) {
                assert(addr0[j] == addr1[j]);
            }
        }

        l_tree(p, leaf0, wots_pk0, pub_seed, addr0);
        l_tree(p, leaf0, wots_pk1, pub_seed, addr1);

        if (!memcmp(leaf0, leaf1, p->n) && !memcmp(wots_pk0, wots_pk1, p->wots_sig_bytes)) {
            printf("[l_tree]: Changing index %ld of the address does not change the result\n", i);
        }

        if (memcmp(leaf0, leaf1, p->n) || memcmp(wots_pk0, wots_pk1, p->wots_sig_bytes)) {
            printf("[l_tree]: Changing index %ld of the address changes the result\n", i);
        }
    }
}

void test_pre_thash_h(const xmss_params *p) {
    assert(p != NULL);
    uint8_t out0[p->n], out1[p->n], pub_seed[p->n];
    uint8_t in[2 * p->n];
    uint32_t addr0[8], addr1[8];

    for (size_t i = 0; i < 8; i++) {
        randombytes(pub_seed, p->n * sizeof(uint8_t));
        randombytes(in, 2 * p->n * sizeof(uint8_t));

        memset(out1, -1, p->n);
        memset(out0, -1, p->n);

        randombytes((uint8_t *)addr0, 8 * sizeof(uint32_t));
        memcpy(addr1, addr0, 8 * sizeof(uint32_t));
        assert(!memcmp(addr0, addr1, 8 * sizeof(uint32_t)));

        flip_addr(addr1, i);
        assert(addr0[i] != addr1[i]);

        for (size_t j = 0; j < 8; j++) {
            if (j != i) {
                assert(addr0[j] == addr1[j]);
            }
        }

        thash_h(p, out0, in, pub_seed, addr0);
        thash_h(p, out1, in, pub_seed, addr1);

        if (!memcmp(out0, out1, p->n * sizeof(uint8_t))) {
            printf("[thash_h]: Changing index %ld of the address does not change the result\n", i);
        } else {
            printf("[thash_h]: Changing index %ld of the address changes the result\n", i);
        }
    }
}

void test_pre(const xmss_params *p) {
    assert(p != NULL);

    puts("================================================================");
    puts("                       #PRE");
    puts("================================================================");

    test_pre_wots_pk_gen(p);
    // test_pre_expand_seed(p);
    // test_pre_gen_chain_inplace(p);
    // test_pre_ltree(p);
    // test_pre_thash_h(p);
}

void test_post_wots_pk_gen(const xmss_params *p) {
    assert(p != NULL);

    uint8_t pub_seed[p->n], sk_seed[p->n];
    uint8_t pk[p->wots_sig_bytes];
    uint32_t addr_before[8], addr_after[8];

    randombytes(pub_seed, p->n * sizeof(uint8_t));
    randombytes(sk_seed, p->n * sizeof(uint8_t));
    memset(addr_before, -1, 8 * sizeof(uint32_t));
    memcpy(addr_after, addr_before, 8 * sizeof(uint32_t));
    assert(!memcmp(addr_before, addr_after, 8 * sizeof(uint32_t)));
    wots_pkgen(p, pk, sk_seed, pub_seed, addr_after);
    print_diff_addr("wots pk gen", addr_before, addr_after);
}

void test_post_expand_seed(const xmss_params *p) {
    uint8_t buf0[p->n], buf1[p->n];
    uint8_t pk[p->wots_sig_bytes];
    uint32_t addr_before[8], addr_after[8];

    randombytes(buf0, p->n * sizeof(uint8_t));
    randombytes(buf1, p->n * sizeof(uint8_t));

    // Post: addr[5] = len - 1 /\ addr[6] = 0 /\ addr[7] = 0
    memset(addr_before, -1, 8 * sizeof(uint32_t));
    memcpy(addr_after, addr_before, 8 * sizeof(uint32_t));
    assert(!memcmp(addr_before, addr_after, 8 * sizeof(uint32_t)));
    expand_seed(p, pk, buf0, buf1, addr_after);
    print_diff_addr("expand seed", addr_before, addr_after);
}

void test_post_gen_chain(const xmss_params *p) {
    assert(p != NULL);

    uint8_t buf0[p->n], buf1[p->n];
    uint32_t addr_before[8], addr_after[8];

    randombytes(buf0, p->n * sizeof(uint8_t));
    randombytes(buf1, p->n * sizeof(uint8_t));

    // Post: addr[6] = MIN (start + steps - 1, w - 1) /\ addr[7] = 1
    memset(addr_before, -1, 8 * sizeof(uint32_t));
    memcpy(addr_after, addr_before, 8 * sizeof(uint32_t));
    assert(!memcmp(addr_before, addr_after, 8 * sizeof(uint32_t)));
    gen_chain(p, buf0, buf0, 0, 10, buf1, addr_after);
    print_diff_addr("gen_chain_inplace", addr_before, addr_after);
}

void test_post_l_tree(const xmss_params *p) {
    assert(p != NULL);

    uint8_t pub_seed[p->n];
    uint8_t leaf[p->n];
    uint8_t wots_pk[p->wots_sig_bytes];
    uint32_t addr_before[8], addr_after[8];

    randombytes(pub_seed, p->n * sizeof(uint8_t));
    randombytes(wots_pk, p->wots_sig_bytes);
    memset(addr_before, -1, 8 * sizeof(uint32_t));
    memcpy(addr_after, addr_before, 8 * sizeof(uint32_t));
    assert(!memcmp(addr_before, addr_after, 8 * sizeof(uint32_t)));

    l_tree(p, leaf, wots_pk, pub_seed, addr_after);
    print_diff_addr("l_tree", addr_before, addr_after);
}

void test_post_thash_h(const xmss_params *p) {
    assert(p != NULL);

    uint8_t out[p->n], pub_seed[p->n], in[2 * p->n];
    uint32_t addr_before[8], addr_after[8];

    randombytes(in, 2 * p->n * sizeof(uint8_t));
    randombytes(pub_seed, p->n * sizeof(uint8_t));

    memset(addr_before, -1, 8 * sizeof(uint32_t));
    memcpy(addr_after, addr_before, 8 * sizeof(uint32_t));
    assert(!memcmp(addr_before, addr_after, 8 * sizeof(uint32_t)));
    thash_h(p, out, in, pub_seed, addr_after);
    print_diff_addr("thash_h", addr_before, addr_after);
}

void test_post(const xmss_params *p) {
    assert(p != NULL);

    puts("================================================================");
    puts("                       #POST");
    puts("================================================================");

    test_post_wots_pk_gen(p);
    // test_post_expand_seed(p);
    // test_post_gen_chain(p);
    // test_post_l_tree(p);
    // test_post_thash_h(p);
}

void test_ltree_prop(const xmss_params *p) {
    assert(p != NULL);

    uint8_t pub_seed[p->n];
    uint8_t leaf[p->n];
    uint8_t wots_pk[p->wots_sig_bytes];
    uint32_t addr[8];

    for (int t = 0; t < 100; t++) {
        randombytes(pub_seed, p->n * sizeof(uint8_t));
        randombytes((uint8_t *)addr, 8 * sizeof(uint32_t));
        randombytes(wots_pk, p->wots_sig_bytes);
        l_tree(p, leaf, wots_pk, pub_seed, addr);

        assert(addr[5] == 7);
        assert(addr[6] == 0);
        assert(addr[7] == 2);
    }

    puts("[l_tree]: addr[5] == 7)");
    puts("[l_tree]: addr[6] == 0)");
    puts("[l_tree]: addr[7] == 2)");
}

void test_prop(const xmss_params *p) {
    assert(p != NULL);

    puts("================================================================");
    puts("                       PROPERTIES");
    puts("================================================================");

    test_ltree_prop(p);
}

int main(void) {
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

    test_pre(&p);
    test_post(&p);
    test_prop(&p);

    return 0;
}