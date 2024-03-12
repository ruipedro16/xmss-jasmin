#include <assert.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "hash_address.h"
#include "print.h"
#include "randombytes.h"

#ifndef TESTS
#define TESTS 10000
#endif

extern void set_layer_addr_jazz(uint32_t *, uint32_t);
extern void set_tree_addr_jazz(uint32_t *, uint64_t);
extern void set_type_jazz(uint32_t *, uint32_t);
extern void set_key_and_mask_jazz(uint32_t *, uint32_t);
extern void copy_subtree_addr_jazz(uint32_t *, const uint32_t *);
extern void set_ots_addr_jazz(uint32_t *, uint32_t);
extern void set_chain_addr_jazz(uint32_t *, uint32_t);
extern void set_hash_addr_jazz(uint32_t *, uint32_t);
extern void set_ltree_addr_jazz(uint32_t *, uint32_t);
extern void set_tree_height_jazz(uint32_t *, uint32_t);
extern void set_tree_index_jazz(uint32_t *, uint32_t);

void test_set_layer_addr(void) {
    bool debug = true;

    uint32_t addr_ref[8], addr_jazz[8];
    uint32_t layer;

    for (int i = 0; i < TESTS; i++) {
        if (debug) {
            printf("[set_layer_addr] Test %d/%d\n", i, TESTS);
        }

        randombytes((uint8_t *)addr_ref, 8 * sizeof(uint32_t));
        memcpy(addr_jazz, addr_ref, 8 * sizeof(uint32_t));

        randombytes((uint8_t *)&layer, sizeof(uint32_t));

        assert(memcmp(addr_ref, addr_jazz, 8 * sizeof(uint32_t)) == 0);

        set_layer_addr_jazz(addr_jazz, layer);
        set_layer_addr(addr_ref, layer);

        if (memcmp(addr_ref, addr_jazz, 8 * sizeof(uint32_t)) != 0) {
            print_str_u8("ADDR REF", (uint8_t *)addr_ref, 8 * sizeof(uint32_t));
            print_str_u8("ADDR JAZZ", (uint8_t *)addr_jazz, 8 * sizeof(uint32_t));
        }

        assert(memcmp(addr_ref, addr_jazz, 8 * sizeof(uint32_t)) == 0);
    }
}

void test_set_tree_addr(void) {
    bool debug = true;

    uint32_t addr_ref[8], addr_jazz[8];
    uint64_t tree;

    for (int i = 0; i < TESTS; i++) {
        if (debug) {
            printf("[set_tree_addr] Test %d/%d\n", i, TESTS);
        }

        randombytes((uint8_t *)addr_ref, 8 * sizeof(uint32_t));
        memcpy(addr_jazz, addr_ref, 8 * sizeof(uint32_t));

        randombytes((uint8_t *)&tree, sizeof(uint64_t));

        assert(memcmp(addr_ref, addr_jazz, 8 * sizeof(uint32_t)) == 0);

        set_tree_addr_jazz(addr_jazz, tree);
        set_tree_addr(addr_ref, tree);

        if (memcmp(addr_ref, addr_jazz, 8 * sizeof(uint32_t)) != 0) {
            print_str_u8("ADDR REF", (uint8_t *)addr_ref, 8 * sizeof(uint32_t));
            print_str_u8("ADDR JAZZ", (uint8_t *)addr_jazz, 8 * sizeof(uint32_t));
        }

        assert(memcmp(addr_ref, addr_jazz, 8 * sizeof(uint32_t)) == 0);
    }
}

void test_set_type(void) {
    bool debug = true;

    uint32_t addr_ref[8], addr_jazz[8];
    uint32_t type;

    for (int i = 0; i < TESTS; i++) {
        if (debug) {
            printf("[set_type] Test %d/%d\n", i, TESTS);
        }

        randombytes((uint8_t *)addr_ref, 8 * sizeof(uint32_t));
        memcpy(addr_jazz, addr_ref, 8 * sizeof(uint32_t));

        randombytes((uint8_t *)&type, sizeof(uint32_t));

        assert(memcmp(addr_ref, addr_jazz, 8 * sizeof(uint32_t)) == 0);

        set_type_jazz(addr_jazz, type);
        set_type(addr_ref, type);

        if (memcmp(addr_ref, addr_jazz, 8 * sizeof(uint32_t)) != 0) {
            print_str_u8("ADDR REF", (uint8_t *)addr_ref, 8 * sizeof(uint32_t));
            print_str_u8("ADDR JAZZ", (uint8_t *)addr_jazz, 8 * sizeof(uint32_t));
        }

        assert(memcmp(addr_ref, addr_jazz, 8 * sizeof(uint32_t)) == 0);
    }
}

void test_set_key_and_mask(void) {
    bool debug = true;

    uint32_t addr_ref[8], addr_jazz[8];
    uint32_t key_and_mask;

    for (int i = 0; i < TESTS; i++) {
        if (debug) {
            printf("[set_key_and_mask] Test %d/%d\n", i, TESTS);
        }

        randombytes((uint8_t *)addr_ref, 8 * sizeof(uint32_t));
        memcpy(addr_jazz, addr_ref, 8 * sizeof(uint32_t));

        randombytes((uint8_t *)&key_and_mask, sizeof(uint32_t));

        assert(memcmp(addr_ref, addr_jazz, 8 * sizeof(uint32_t)) == 0);

        set_key_and_mask_jazz(addr_jazz, key_and_mask);
        set_key_and_mask(addr_ref, key_and_mask);

        if (memcmp(addr_ref, addr_jazz, 8 * sizeof(uint32_t)) != 0) {
            print_str_u8("ADDR REF", (uint8_t *)addr_ref, 8 * sizeof(uint32_t));
            print_str_u8("ADDR JAZZ", (uint8_t *)addr_jazz, 8 * sizeof(uint32_t));
        }

        assert(memcmp(addr_ref, addr_jazz, 8 * sizeof(uint32_t)) == 0);
    }
}

void test_copy_subtree_addr_jazz(void) {
    bool debug = true;

    uint32_t in_ref[8], in_jazz[8];
    uint32_t out_ref[8], out_jazz[8];

    for (int i = 0; i < TESTS; i++) {
        if (debug) {
            printf("[copy_subtree_addr] Test %d/%d\n", i, TESTS);
        }

        randombytes((uint8_t *)in_ref, 8 * sizeof(uint32_t));
        memcpy(in_jazz, in_ref, 8 * sizeof(uint32_t));

        randombytes((uint8_t *)out_ref, 8 * sizeof(uint32_t));
        memcpy(out_jazz, out_ref, 8 * sizeof(uint32_t));

        assert(memcmp(in_ref, in_jazz, 8 * sizeof(uint32_t)) == 0);
        assert(memcmp(out_ref, out_jazz, 8 * sizeof(uint32_t)) == 0);

        copy_subtree_addr_jazz(out_jazz, in_jazz);
        copy_subtree_addr(out_ref, in_ref);

        if (memcmp(out_ref, out_jazz, 8 * sizeof(uint32_t)) != 0) {
            print_str_u8("OUT REF", (uint8_t *)out_ref, 8 * sizeof(uint32_t));
            print_str_u8("OUT JAZZ", (uint8_t *)out_jazz, 8 * sizeof(uint32_t));
        }

        assert(memcmp(out_ref, out_jazz, 8 * sizeof(uint32_t)) == 0);
    }
}

void test_set_ots_addr(void) {
    bool debug = true;

    uint32_t addr_ref[8], addr_jazz[8];
    uint32_t ots_adr;

    for (int i = 0; i < TESTS; i++) {
        if (debug) {
            printf("[set_ots_addr] Test %d/%d\n", i, TESTS);
        }

        randombytes((uint8_t *)addr_ref, 8 * sizeof(uint32_t));
        memcpy(addr_jazz, addr_ref, 8 * sizeof(uint32_t));

        randombytes((uint8_t *)&ots_adr, sizeof(uint32_t));

        assert(memcmp(addr_ref, addr_jazz, 8 * sizeof(uint32_t)) == 0);

        set_ots_addr_jazz(addr_jazz, ots_adr);
        set_ots_addr(addr_ref, ots_adr);

        if (memcmp(addr_ref, addr_jazz, 8 * sizeof(uint32_t)) != 0) {
            print_str_u8("ADDR REF", (uint8_t *)addr_ref, 8 * sizeof(uint32_t));
            print_str_u8("ADDR JAZZ", (uint8_t *)addr_jazz, 8 * sizeof(uint32_t));
        }

        assert(memcmp(addr_ref, addr_jazz, 8 * sizeof(uint32_t)) == 0);
    }
}

void test_set_chain_addr(void) {
    bool debug = true;

    uint32_t addr_ref[8], addr_jazz[8];
    uint32_t chain_adr;

    for (int i = 0; i < TESTS; i++) {
        if (debug) {
            printf("[set_chain_addr] Test %d/%d\n", i, TESTS);
        }

        randombytes((uint8_t *)addr_ref, 8 * sizeof(uint32_t));
        memcpy(addr_jazz, addr_ref, 8 * sizeof(uint32_t));

        randombytes((uint8_t *)&chain_adr, sizeof(uint32_t));

        assert(memcmp(addr_ref, addr_jazz, 8 * sizeof(uint32_t)) == 0);

        set_chain_addr_jazz(addr_jazz, chain_adr);
        set_chain_addr(addr_ref, chain_adr);

        if (memcmp(addr_ref, addr_jazz, 8 * sizeof(uint32_t)) != 0) {
            print_str_u8("ADDR REF", (uint8_t *)addr_ref, 8 * sizeof(uint32_t));
            print_str_u8("ADDR JAZZ", (uint8_t *)addr_jazz, 8 * sizeof(uint32_t));
        }

        assert(memcmp(addr_ref, addr_jazz, 8 * sizeof(uint32_t)) == 0);
    }
}

void test_set_hash_addr(void) {
    bool debug = true;

    uint32_t addr_ref[8], addr_jazz[8];
    uint32_t hash_adr;

    for (int i = 0; i < TESTS; i++) {
        if (debug) {
            printf("[set_hash_addr] Test %d/%d\n", i, TESTS);
        }

        randombytes((uint8_t *)addr_ref, 8 * sizeof(uint32_t));
        memcpy(addr_jazz, addr_ref, 8 * sizeof(uint32_t));

        randombytes((uint8_t *)&hash_adr, sizeof(uint32_t));

        assert(memcmp(addr_ref, addr_jazz, 8 * sizeof(uint32_t)) == 0);

        set_hash_addr_jazz(addr_jazz, hash_adr);
        set_hash_addr(addr_ref, hash_adr);

        if (memcmp(addr_ref, addr_jazz, 8 * sizeof(uint32_t)) != 0) {
            print_str_u8("ADDR REF", (uint8_t *)addr_ref, 8 * sizeof(uint32_t));
            print_str_u8("ADDR JAZZ", (uint8_t *)addr_jazz, 8 * sizeof(uint32_t));
        }

        assert(memcmp(addr_ref, addr_jazz, 8 * sizeof(uint32_t)) == 0);
    }
}

void test_set_ltree_addr(void) {
    bool debug = true;

    uint32_t addr_ref[8], addr_jazz[8];
    uint32_t ltree;

    for (int i = 0; i < TESTS; i++) {
        if (debug) {
            printf("[set_ltree_addr] Test %d/%d\n", i, TESTS);
        }

        randombytes((uint8_t *)addr_ref, 8 * sizeof(uint32_t));
        memcpy(addr_jazz, addr_ref, 8 * sizeof(uint32_t));

        randombytes((uint8_t *)&ltree, sizeof(uint32_t));

        assert(memcmp(addr_ref, addr_jazz, 8 * sizeof(uint32_t)) == 0);

        set_ltree_addr_jazz(addr_jazz, ltree);
        set_ltree_addr(addr_ref, ltree);

        if (memcmp(addr_ref, addr_jazz, 8 * sizeof(uint32_t)) != 0) {
            print_str_u8("ADDR REF", (uint8_t *)addr_ref, 8 * sizeof(uint32_t));
            print_str_u8("ADDR JAZZ", (uint8_t *)addr_jazz, 8 * sizeof(uint32_t));
        }

        assert(memcmp(addr_ref, addr_jazz, 8 * sizeof(uint32_t)) == 0);
    }
}

void test_set_tree_height(void) {
    bool debug = true;

    uint32_t addr_ref[8], addr_jazz[8];
    uint32_t tree_height;

    for (int i = 0; i < TESTS; i++) {
        if (debug) {
            printf("[set_tree_height] Test %d/%d\n", i, TESTS);
        }

        randombytes((uint8_t *)addr_ref, 8 * sizeof(uint32_t));
        memcpy(addr_jazz, addr_ref, 8 * sizeof(uint32_t));

        randombytes((uint8_t *)&tree_height, sizeof(uint32_t));

        assert(memcmp(addr_ref, addr_jazz, 8 * sizeof(uint32_t)) == 0);

        set_tree_height_jazz(addr_jazz, tree_height);
        set_tree_height(addr_ref, tree_height);

        if (memcmp(addr_ref, addr_jazz, 8 * sizeof(uint32_t)) != 0) {
            print_str_u8("ADDR REF", (uint8_t *)addr_ref, 8 * sizeof(uint32_t));
            print_str_u8("ADDR JAZZ", (uint8_t *)addr_jazz, 8 * sizeof(uint32_t));
        }

        assert(memcmp(addr_ref, addr_jazz, 8 * sizeof(uint32_t)) == 0);
    }
}

void test_set_tree_index(void) {
    bool debug = true;

    uint32_t addr_ref[8], addr_jazz[8];
    uint32_t tree_index;

    for (int i = 0; i < TESTS; i++) {
        if (debug) {
            printf("[set_tree_index] Test %d/%d\n", i, TESTS);
        }

        randombytes((uint8_t *)addr_ref, 8 * sizeof(uint32_t));
        memcpy(addr_jazz, addr_ref, 8 * sizeof(uint32_t));

        randombytes((uint8_t *)&tree_index, sizeof(uint32_t));

        assert(memcmp(addr_ref, addr_jazz, 8 * sizeof(uint32_t)) == 0);

        set_tree_index_jazz(addr_jazz, tree_index);
        set_tree_index(addr_ref, tree_index);

        if (memcmp(addr_ref, addr_jazz, 8 * sizeof(uint32_t)) != 0) {
            print_str_u8("ADDR REF", (uint8_t *)addr_ref, 8 * sizeof(uint32_t));
            print_str_u8("ADDR JAZZ", (uint8_t *)addr_jazz, 8 * sizeof(uint32_t));
        }

        assert(memcmp(addr_ref, addr_jazz, 8 * sizeof(uint32_t)) == 0);
    }
}

int main() {
    test_set_layer_addr();
    test_set_tree_addr();
    test_set_type();
    test_set_key_and_mask();
    test_copy_subtree_addr_jazz();
    test_set_ots_addr();
    test_set_chain_addr();
    test_set_hash_addr();
    test_set_ltree_addr();
    test_set_tree_height();
    printf("Hash Address: OK\n");
    return 0;
}