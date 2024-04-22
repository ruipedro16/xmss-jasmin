#include "xmss_core.h"

#include <stdint.h>
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

#ifdef TEST_PRF
extern void prf_jazz(uint8_t *, const uint8_t *, const uint8_t *);
#endif

#ifdef TEST_THASH_H
extern void thash_h_jazz(uint8_t *, uint32_t *, const uint8_t *, const uint8_t *);
#endif

#ifdef TEST_HASH_MESSAGE
extern void hash_message_jazz(uint8_t *, const uint8_t *, const uint8_t *, uint64_t, const uint8_t *, size_t);
#endif

#ifdef TEST_GEN_LEAF_WOTS
extern void gen_leaf_wots_jazz(uint8_t *leaf, uint32_t ltree_addr[8], uint32_t ots_addr[8], const uint8_t *sk_seed,
                               const uint8_t *pub_seed);
#endif

#ifdef TEST_TREEHASH_ARRAY
extern void treehash_array_jazz(unsigned char *root, unsigned char *auth_path, const unsigned char *sk_seed,
                                const unsigned char *pub_seed, uint32_t leaf_idx, const uint32_t subtree_addr[8]);
#endif

#ifdef TEST_KEYPAIR_SEED
extern int xmssmt_core_seed_keypair_jazz(uint8_t *pk, uint8_t *sk, const uint8_t *seed);
#endif

/**
 * For a given leaf index, computes the authentication path and the resulting
 * root node using Merkle's TreeHash algorithm.
 * Expects the layer and tree parts of subtree_addr to be set.
 */
void treehash(const xmss_params *params, unsigned char *root, unsigned char *auth_path, const unsigned char *sk_seed,
              const unsigned char *pub_seed, uint32_t leaf_idx, const uint32_t subtree_addr[8]) {
    unsigned char stack[(params->tree_height + 1) * params->n];
    unsigned int heights[params->tree_height + 1];
    unsigned int offset = 0;

    /* The subtree has at most 2^20 leafs, so uint32_t suffices. */
    uint32_t idx;
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

    for (idx = 0; idx < (uint32_t)(1 << params->tree_height); idx++) {
        /* Add the next leaf node to the stack. */
        set_ltree_addr(ltree_addr, idx);
        set_ots_addr(ots_addr, idx);

#ifdef TEST_GEN_LEAF_WOTS
        gen_leaf_wots_jazz(stack + offset * params->n, ltree_addr, ots_addr, sk_seed, pub_seed);
#else
        gen_leaf_wots(params, stack + offset * params->n, sk_seed, pub_seed, ltree_addr, ots_addr);
#endif

        offset++;
        heights[offset - 1] = 0;

        /* If this is a node we need for the auth path.. */
        if ((leaf_idx ^ 0x1) == idx) {
            memcpy(auth_path, stack + (offset - 1) * params->n, params->n);
        }

        while (offset >= 2 && heights[offset - 1] == heights[offset - 2]) {
            tree_idx = (idx >> (heights[offset - 1] + 1));

            set_tree_height(node_addr, heights[offset - 1]);
            set_tree_index(node_addr, tree_idx);

#ifdef TEST_THASH_H
            // NOTE: in the jasmin impl, addr is the 2nd argument because writable ptrs must come first in the arguments
            thash_h_jazz(stack + (offset - 2) * params->n, node_addr, stack + (offset - 2) * params->n, pub_seed);
#else
            thash_h(params, stack + (offset - 2) * params->n, stack + (offset - 2) * params->n, pub_seed, node_addr);
#endif

            offset--;
            heights[offset - 1]++;

            if (((leaf_idx >> heights[offset - 1]) ^ 0x1) == tree_idx) {
                memcpy(auth_path + heights[offset - 1] * params->n, stack + (offset - 1) * params->n, params->n);
            }
        }
    }
    memcpy(root, stack, params->n);
}

/**
 * Given a set of parameters, this function returns the size of the secret key.
 * This is implementation specific, as varying choices in tree traversal will
 * result in varying requirements for state storage.
 */
unsigned long long xmss_xmssmt_core_sk_bytes(const xmss_params *params) { return params->index_bytes + 4 * params->n; }

/*
 * Generates a XMSS key pair for a given parameter set.
 * Format sk: [(32bit) index || SK_SEED || SK_PRF || root || PUB_SEED]
 * Format pk: [root || PUB_SEED], omitting algorithm OID.
 */
int xmss_core_keypair(const xmss_params *params, unsigned char *pk, unsigned char *sk) {
    /* The key generation procedure of XMSS and XMSSMT is exactly the same.
       The only important detail is that the right subtree must be selected;
       this requires us to correctly set the d=1 parameter for XMSS. */
    return xmssmt_core_keypair(params, pk, sk);
}

/**
 * Signs a message. Returns an array containing the signature followed by the
 * message and an updated secret key.
 */
int xmss_core_sign(const xmss_params *params, unsigned char *sk, unsigned char *sm, unsigned long long *smlen,
                   const unsigned char *m, unsigned long long mlen) {
    /* XMSS signatures are fundamentally an instance of XMSSMT signatures.
       For d=1, as is the case with XMSS, some of the calls in the XMSSMT
       routine become vacuous (i.e. the loop only iterates once, and address
       management can be simplified a bit).*/
    return xmssmt_core_sign(params, sk, sm, smlen, m, mlen);
}

/*
 * Derives a XMSSMT key pair for a given parameter set.
 * Seed must be 3*n long.
 * Format sk: [(ceil(h/8) bit) index || SK_SEED || SK_PRF || root || PUB_SEED]
 * Format pk: [root || PUB_SEED] omitting algorithm OID.
 */
int xmssmt_core_seed_keypair(const xmss_params *params, unsigned char *pk, unsigned char *sk, unsigned char *seed) {
    /* We do not need the auth path in key generation, but it simplifies the
       code to have just one treehash routine that computes both root and path
       in one function. */
    unsigned char auth_path[params->tree_height * params->n];
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

/* Compute root node of the top-most subtree. */
#ifdef TEST_TREEHASH_ARRAY
    // NOTE: auth path is first because in jasmin mutable arrays must come first
    puts("DEBUG: TREEHASH ARRAY JASMIN IMPL");
    treehash_array_jazz(pk, auth_path, sk, pk + params->n, 0, top_tree_addr);
#else
    treehash(params, pk, auth_path, sk, pk + params->n, 0, top_tree_addr);
#endif

    memcpy(sk + 2 * params->n, pk, params->n);

    return 0;
}

/*
 * Generates a XMSSMT key pair for a given parameter set.
 * Format sk: [(ceil(h/8) bit) index || SK_SEED || SK_PRF || root || PUB_SEED]
 * Format pk: [root || PUB_SEED] omitting algorithm OID.
 */
int xmssmt_core_keypair(const xmss_params *params, unsigned char *pk, unsigned char *sk) {
    unsigned char seed[3 * params->n];

    randombytes(seed, 3 * params->n);
#ifdef TEST_KEYPAIR_SEED
    puts("DEBUG: SEED KEYPAIR JASMIN IMPL");
    xmssmt_core_seed_keypair_jazz(pk, sk, seed);
#else
    xmssmt_core_seed_keypair(params, pk, sk, seed);
#endif

    return 0;
}

/**
 * Signs a message. Returns an array containing the signature followed by the
 * message and an updated secret key.
 */
int xmssmt_core_sign(const xmss_params *params, unsigned char *sk, unsigned char *sm, unsigned long long *smlen,
                     const unsigned char *m, unsigned long long mlen) {
    const unsigned char *sk_seed = sk + params->index_bytes;
    const unsigned char *sk_prf = sk + params->index_bytes + params->n;
    const unsigned char *pub_root = sk + params->index_bytes + 2 * params->n;
    const unsigned char *pub_seed = sk + params->index_bytes + 3 * params->n;

    unsigned char root[params->n];
    unsigned char *mhash = root;
    unsigned long long idx;
    unsigned char idx_bytes_32[32];
    unsigned int i;
    uint32_t idx_leaf;

    uint32_t ots_addr[8] = {0};
    set_type(ots_addr, XMSS_ADDR_TYPE_OTS);

    /* Already put the message in the right place, to make it easier to prepend
     * things when computing the hash over the message. */
    memcpy(sm + params->sig_bytes, m, mlen);
    *smlen = params->sig_bytes + mlen;

    /* Read and use the current index from the secret key. */
    idx = (unsigned long)bytes_to_ull(sk, params->index_bytes);

    /* Check if we can still sign with this sk.
     * If not, return -2
     *
     * If this is the last possible signature (because the max index value
     * is reached), production implementations should delete the secret key
     * to prevent accidental further use.
     *
     * For the case of total tree height of 64 we do not use the last signature
     * to be on the safe side (there is no index value left to indicate that the
     * key is finished, hence external handling would be necessary)
     */
    if (idx >= ((1ULL << params->full_height) - 1)) {
        // Delete secret key here. We only do this in memory, production code
        // has to make sure that this happens on disk.
        memset(sk, 0xFF, params->index_bytes);
        memset(sk + params->index_bytes, 0, (params->sk_bytes - params->index_bytes));
        if (idx > ((1ULL << params->full_height) - 1)) return -2;  // We already used all one-time keys
        if ((params->full_height == 64) && (idx == ((1ULL << params->full_height) - 1)))
            return -2;  // We already used all one-time keys
    }

    memcpy(sm, sk, params->index_bytes);

    /*************************************************************************
     * THIS IS WHERE PRODUCTION IMPLEMENTATIONS WOULD UPDATE THE SECRET KEY. *
     *************************************************************************/
    /* Increment the index in the secret key. */
    ull_to_bytes(sk, params->index_bytes, idx + 1);

    /* Compute the digest randomization value. */
    ull_to_bytes(idx_bytes_32, 32, idx);

#ifdef TEST_PRF
    prf_jazz(sm + params->index_bytes, idx_bytes_32, sk_prf);
#else
    prf(params, sm + params->index_bytes, idx_bytes_32, sk_prf);
#endif

/* Compute the message hash. */
#ifdef TEST_HASH_MESSAGE
    hash_message_jazz(mhash, sm + params->index_bytes, pub_root, idx,
                      sm + params->sig_bytes - params->padding_len - 3 * params->n, mlen);
#else
    hash_message(params, mhash, sm + params->index_bytes, pub_root, idx,
                 sm + params->sig_bytes - params->padding_len - 3 * params->n, mlen);
#endif

    sm += params->index_bytes + params->n;

    set_type(ots_addr, XMSS_ADDR_TYPE_OTS);

    for (i = 0; i < params->d; i++) {
        idx_leaf = (idx & ((1 << params->tree_height) - 1));
        idx = idx >> params->tree_height;

        set_layer_addr(ots_addr, i);
        set_tree_addr(ots_addr, idx);
        set_ots_addr(ots_addr, idx_leaf);

        /* Compute a WOTS signature. */
        /* Initially, root = mhash, but on subsequent iterations it is the root
           of the subtree below the currently processed subtree. */
        wots_sign(params, sm, root, sk_seed, pub_seed, ots_addr);
        sm += params->wots_sig_bytes;

/* Compute the authentication path for the used WOTS leaf. */
#ifdef TEST_TREEHASH_ARRAY
        puts("DEBUG: TREEHASH ARRAY JASMIN IMPL 2");
        treehash_array_jazz(root, sm, sk_seed, pub_seed, idx_leaf, ots_addr);
#else
        treehash(params, root, sm, sk_seed, pub_seed, idx_leaf, ots_addr);
#endif

        sm += params->tree_height * params->n;
    }

    return 0;
}
