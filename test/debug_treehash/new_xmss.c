#include "new_xmss.h"

#include <assert.h>
#include <inttypes.h>
#include <math.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "hash.h"
#include "hash_address.h"
#include "params.h"
#include "print.h"
#include "randombytes.h"
#include "utils.h"
#include "wots.h"
#include "xmss_commons.h"

bool debug_treehash = true;

void treehash_new(const xmss_params *params, unsigned char *root, const unsigned char *sk_seed,
                  const unsigned char *pub_seed, uint32_t start_index, /* leaf_idx in the old impl */
                  uint32_t target_height, const uint32_t subtree_addr[8]) {
    unsigned char stack[(params->tree_height + 1) * params->n];
    unsigned int heights[params->tree_height + 1];
    unsigned int offset = 0;

    /* The subtree has at most 2^20 leafs, so uint32_t suffices. */
    uint32_t i;
    uint32_t tree_idx;

    /* We need all three types of addresses in parallel. */
    uint32_t ots_addr[8] = {0};
    uint32_t ltree_addr[8] = {0};
    uint32_t node_addr[8] = {0};

    /* Select the required subtree. */
    copy_subtree_addr(ots_addr, subtree_addr);
    copy_subtree_addr(ltree_addr, subtree_addr);
    copy_subtree_addr(node_addr, subtree_addr);

    set_type(ots_addr, XMSS_ADDR_TYPE_OTS);
    set_type(ltree_addr, XMSS_ADDR_TYPE_LTREE);
    set_type(node_addr, XMSS_ADDR_TYPE_HASHTREE);

    for (i = 0; i < (uint32_t)(1 << target_height); i++) {
        /* Add the next leaf node to the stack. */
        set_ltree_addr(ltree_addr, start_index + i);
        set_ots_addr(ots_addr, start_index + i);
        gen_leaf_wots(params, stack + offset * params->n, sk_seed, pub_seed, ltree_addr, ots_addr);

        offset++;
        heights[offset - 1] = 0;

        /* While the top-most nodes are of equal height.. */
        while (offset >= 2 &&
               heights[offset - 1] == heights[offset - 2]) { /* Obs: In jasmin, the second part of && is unsafe because
                                                                it doesnt short circuitS */
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
        }
    }

    memcpy(root, stack, params->n);
}

void build_auth_path(const xmss_params *params,
                     uint8_t *auth_path,  // size XMSS_TREE_HEIGHT * XMSS_N
                     const unsigned char *sk_seed, const unsigned char *pub_seed,
                     uint32_t i,  // wots+ Key pair index (index of the node on the tree)
                     uint32_t *addr) {
    uint32_t k;
    for (unsigned int j = 0; j < params->tree_height; j++) {
        k = (i >> j) ^ 1;

        treehash_new(params, auth_path, sk_seed, pub_seed, k << j, j, addr);
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

    build_auth_path(params, auth_path, sk_seed, pub_seed, idx_sig, addr);
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

    treehash_new(params, pk, sk, pk + params->n, 0, params->tree_height, top_tree_addr);

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

    idx_leaf = (idx & ((1 << params->tree_height) - 1));
    idx_tree = idx >> params->tree_height;
    set_tree_addr(ots_addr, idx_tree);

    // Sig_tmp = treeSig(M', SK, idx_leaf, ADRS);
    sm += params->index_bytes + params->n;
    treesig(params, sm, mhash, sk, idx_leaf, ots_addr);
    sm += params->wots_sig_bytes + params->tree_height * params->n;

    // Sig_MT = Sig_MT || r || Sig_tmp;
    // Sig_MT is already set the line 168
    // r is already set in line 176
    // In treesig, we write directly to SM

    for (unsigned int i = 1; i < params->d; i++) {
        treehash_new(params, root, sk_seed, pub_seed, 0, params->tree_height, ots_addr);
        idx_leaf = (idx & ((1 << params->tree_height) - 1));
        idx = idx >> params->tree_height;  // idx_tree

        set_layer_addr(ots_addr, i);
        set_tree_addr(ots_addr, idx_tree);
        // set_ots_addr(ots_addr, idx_leaf); this is done in treesig

        treesig(params, sm, root, sk, idx_leaf, ots_addr);
        sm += params->wots_sig_bytes + params->tree_height * params->n;
    }

    return 0;
}