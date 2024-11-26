#include "new_xmss.h"

#include <assert.h>
#include <inttypes.h>
#include <math.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* We only use this for debugging */
#if 1
#include <unistd.h>
#endif 

#include "hash.h"
#include "hash_address.h"
#include "params.h"
#include "print.h"
#include "randombytes.h"
#include "utils.h"
#include "wots.h"
#include "xmss_commons.h"

bool debug = true;

#define I1 (0 <= offset && offset < size_heights)
#define I2 (1 <= offset && offset <= size_heights)

// This also goes through for I2: (0 <= offset - 2 && offset <= size_heights)

extern void treehash_jazz(uint8_t *root, const uint8_t *sk_seed, const uint8_t *pub_seed, uint32_t start_index,
                          uint32_t target_height, const uint32_t *subtree_addr);

extern void build_auth_path_jazz(uint8_t *auth_path, const uint8_t *sk_seed, const uint8_t *pub_seed, uint32_t i,
                                 uint32_t *addr);

extern void treesig_jazz(uint8_t *sig, uint32_t *addr, const uint8_t *M, const uint8_t *sk, uint32_t idx_sig);

void treehash_new(const xmss_params *params, unsigned char *root, const unsigned char *sk_seed,
                  const unsigned char *pub_seed, uint32_t start_index, /* leaf_idx in the old impl */
                  uint32_t target_height, const uint32_t subtree_addr[8]) {
    unsigned char stack[(params->tree_height + 1) * params->n];
    unsigned int heights[params->tree_height + 1];
    unsigned int offset = 0;

    size_t size_heights = params->tree_height + 1;
    size_t size_stack = params->tree_height + 1;

    /* The subtree has at most 2^20 leafs, so uint32_t suffices. */
    uint32_t i;
    uint32_t tree_idx;

    /* We need all three types of addresses in parallel. */
    uint32_t ots_addr[8];
    uint32_t ltree_addr[8];
    uint32_t node_addr[8];

    memcpy(ots_addr, subtree_addr, 8 * sizeof(uint32_t));
    memcpy(ltree_addr, subtree_addr, 8 * sizeof(uint32_t));
    memcpy(node_addr, subtree_addr, 8 * sizeof(uint32_t));

    set_type(ots_addr, XMSS_ADDR_TYPE_OTS);
    set_type(ltree_addr, XMSS_ADDR_TYPE_LTREE);
    set_type(node_addr, XMSS_ADDR_TYPE_HASHTREE);

    i = 0;
    assert(I1);

    dprintf(4, "size heights = %ld\n", size_heights);
    dprintf(4, "size stack = %ld\n\n\n", size_stack);
    dprintf(5, "size heights = %ld\n", size_heights);
    dprintf(5, "size stack = %ld\n\n\n", size_stack);
    

    dprintf(4, "offset before the outer loop: %d\n\n", offset);
    while (i < (uint32_t)(1 << target_height)) {
        assert(I1);
        dprintf(4, "offset at the start of the iteration (outer loop): %d\n", offset);

        /* Add the next leaf node to the stack. */
        set_ltree_addr(ltree_addr, start_index + i);
        set_ots_addr(ots_addr, start_index + i);
        gen_leaf_wots(params, stack + offset * params->n, sk_seed, pub_seed, ltree_addr, ots_addr);

        offset++;
        heights[offset - 1] = 0;

        assert(I2);
        /* While the top-most nodes are of equal height.. */
        dprintf(5, "[i = %d]: offset before the inner loop: %d\n\n", i, offset);
        while (offset >= 2 && heights[offset - 1] == heights[offset - 2]) {
            assert(I2);
            dprintf(5, "[i = %d] offset at the start of the iteration (inner loop): %d\n", i, offset);

            /* Compute index of the new node, in the next layer. */
            tree_idx = ((start_index + i) >> (heights[offset - 1] + 1));

            /* Hash the top-most nodes from the stack together. */
            /* Note that tree height is the 'lower' layer, even though we use
               the index of the new node on the 'higher' layer. This follows
               from the fact that we address the hash function calls. */
            set_tree_height(node_addr, heights[offset - 1]);
            set_tree_index(node_addr, tree_idx);
            thash_h(params, stack + (offset - 2) * params->n, stack + (offset - 2) * params->n, pub_seed, node_addr);
            offset--;
            /* Note that the top-most node is now one layer higher. */
            heights[offset - 1]++;
            dprintf(6, "Heights: %d\n", heights[offset - 1]);

            assert(I2);
            dprintf(5, "[i = %d] offset at the end of the iteration (inner loop): %d\n", i, offset);
        }
        dprintf(5, "[i = %d] offset after the inner loop: %d\n\n", i, offset);
        dprintf(4, "offset at the end of the iteration (outer loop): %d\n\n", offset); // aqui 
        assert(I1);
        assert(I2);
        i += 1;
    }
    assert(I1);
    dprintf(4, "offset at the end of the outer loop: %d\n\n", offset);
    memcpy(root, stack, params->n);
}

void build_auth_path(const xmss_params *params,
                     uint8_t *auth_path,  // size XMSS_TREE_HEIGHT * XMSS_N
                     const unsigned char *sk_seed, const unsigned char *pub_seed,
                     uint32_t i,  // wots+ Key pair index (index of the node on the tree)
                     uint32_t *addr) {
    uint32_t k;
    for (unsigned int j = 0; j < params->tree_height; j++) {
        k = ((i >> j) ^ 1) << j;

        treehash_new(params, auth_path, sk_seed, pub_seed, k, j, addr);
        auth_path += params->n;
    }
}

// treesig
void treesig(const xmss_params *params, unsigned char *sig /* reduced signature =  wots signature || auth path */,
             const unsigned char *M, unsigned char *sk, uint32_t idx_sig, uint32_t *addr) {
    unsigned char sig_ots[params->wots_sig_bytes];
    unsigned char auth_path[params->tree_height + 1 * params->n];

    unsigned char *sk_seed = sk + params->index_bytes;
    unsigned char *pub_seed = sk + params->index_bytes + 3 * params->n;

    set_type(addr, XMSS_ADDR_TYPE_OTS);
    set_ots_addr(addr, idx_sig);

    wots_sign(params, sig_ots, M, sk_seed, pub_seed, addr);
    memcpy(sig, sig_ots, params->wots_sig_bytes);

#ifdef TEST_AUTH_PATH
    if (debug) {
        puts("Running Jasmin implementation of build auth path");
    }
    build_auth_path_jazz(auth_path, sk_seed, pub_seed, idx_sig, addr);
#else
    build_auth_path(params, auth_path, sk_seed, pub_seed, idx_sig, addr);
#endif

    memcpy(sig + params->wots_sig_bytes, auth_path, params->tree_height * params->n);
}

// keygen
int xmssmt_core_seed_keypair_new(const xmss_params *params, unsigned char *pk, unsigned char *sk,
                                 const unsigned char *seed) {
    /* We do not need the auth path in key generation, but it simplifies the
       code to have just one treehash routine that computes both root and path
       in one function. */
    uint32_t top_tree_addr[8] = {0};

    set_layer_addr(top_tree_addr, params->d - 1);

    /* Initialize index to 0. */
    memset(sk, 0, params->index_bytes);
    sk += params->index_bytes;

    /* Initialize SK_SEED and SK_PRF. */
    memcpy(sk, seed, 2 * params->n);

    /* Initialize PUB_SEED. */
    memcpy(sk + 3 * params->n, seed + 2 * params->n, params->n);
    memcpy(pk + params->n, sk + 3 * params->n, params->n);

#ifdef TEST_TREEHASH
    if (debug) {
        puts("Running Jasmin implementation of treehash");
    }
    treehash_jazz(pk, sk, pk + params->n, 0, params->tree_height, top_tree_addr);
#else
    treehash_new(params, pk, sk, pk + params->n, 0, params->tree_height, top_tree_addr);
#endif

    memcpy(sk + 2 * params->n, pk, params->n);

    return 0;
}

// sign
int xmssmt_core_sign_new(const xmss_params *params, unsigned char *sk, unsigned char *sm, unsigned long long *smlen,
                         const unsigned char *m, unsigned long long mlen) {
    const unsigned char *sk_seed = sk + params->index_bytes;
    const unsigned char *pub_seed = sk + params->index_bytes + 3 * params->n;
    const unsigned char *sk_prf = sk + params->index_bytes + params->n;
    const unsigned char *pub_root = sk + params->index_bytes + 2 * params->n;

    unsigned char root[params->n];
    unsigned char mhash[params->n];
    unsigned long long idx;
    unsigned char idx_bytes_32[32];
    uint32_t idx_tree;

    uint32_t idx_leaf;

    uint32_t ots_addr[8] = {0};
    set_type(ots_addr, XMSS_ADDR_TYPE_OTS);

    /* Already put the message in the right place, to make it easier to prepend
     * things when computing the hash over the message. */
    memcpy(sm + params->sig_bytes, m, mlen);
    *smlen = params->sig_bytes + mlen;

    idx = (unsigned long)bytes_to_ull(sk, params->index_bytes);

    // Check if we can still sign with this sk.
    if (idx >= ((1ULL << params->full_height) - 1)) {
        // Delete secret key here. We only do this in memory, production code
        // has to make sure that this happens on disk.
        memset(sk, 0xFF, params->index_bytes);
        memset(sk + params->index_bytes, 0, (params->sk_bytes - params->index_bytes));
        if (idx > ((1ULL << params->full_height) - 1)) {  // We already used all one-time keys
            return -2;
        }

        if ((params->full_height == 64) &&
            (idx == ((1ULL << params->full_height) - 1))) {  // We already used all one-time keys
            return -2;
        }
    }

    memcpy(sm, sk, params->index_bytes);  // Writes idx to the signature

    /* Increment the index in the secret key. */
    ull_to_bytes(sk, params->index_bytes, idx + 1);  // Writes idx to the key

    /* Compute the digest randomization value. */
    ull_to_bytes(idx_bytes_32, 32, idx);

    prf(params, sm + params->index_bytes, idx_bytes_32, sk_prf);  // Writes R

    /* Compute the message hash. */
    hash_message(params, mhash, sm + params->index_bytes, pub_root, idx,
                 sm + params->sig_bytes - params->padding_len - 3 * params->n, mlen);  // set the root

    set_type(ots_addr, XMSS_ADDR_TYPE_OTS);
    set_layer_addr(ots_addr, 0);

    idx_tree = idx >> params->tree_height;               /* (h - h / d) most significant bits of idx_sig */
    idx_leaf = (idx & ((1 << params->tree_height) - 1)); /* (h - h / d) least significant bits of idx_sig */
    set_tree_addr(ots_addr, idx_tree);

    // Sig_tmp = treeSig(M', SK, idx_leaf, ADRS);
    sm += params->index_bytes + params->n;

#ifdef TEST_TREESIG
    if (debug) {
        puts("Running Jasmin implementation of treesig");
    }

    treesig_jazz(sm, ots_addr, mhash, sk,
                 idx_leaf); /* The second argument is the addr because in jasmin, mutable arrays must come first */
#else
    treesig(params, sm, mhash, sk, idx_leaf, ots_addr);
#endif

    sm += params->wots_sig_bytes + params->tree_height * params->n;

    // Sig_MT = Sig_MT || r || Sig_tmp;
    // Sig_MT is already set the line 168
    // r is already set in line 176
    // In treesig, we write directly to SM

    for (unsigned int i = 1; i < params->d; i++) {
        treehash_new(params, root, sk_seed, pub_seed, 0, params->tree_height, ots_addr);
        idx_tree = idx_tree >> params->tree_height;               /* (h - h / d) most significant bits of idx_sig */
        idx_leaf = (idx_tree & ((1 << params->tree_height) - 1)); /* (h - h / d) least significant bits of idx_sig */

        set_layer_addr(ots_addr, i);
        set_tree_addr(ots_addr, idx);

        treesig(params, sm, root, sk, idx_leaf, ots_addr);
        sm += params->wots_sig_bytes + params->tree_height * params->n;
    }

    return 0;
}