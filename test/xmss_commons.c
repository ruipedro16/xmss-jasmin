#include "xmss_commons.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

#include "hash.h"
#include "hash_address.h"
#include "params.h"
#include "utils.h"
#include "wots.h"
#include "print.h"

#ifdef TEST_THASH_H
extern void thash_h_jazz(uint8_t *, uint32_t *, const uint8_t *, const uint8_t *);
#endif

#ifdef TEST_LTREE
extern void l_tree_jazz(uint8_t *, uint8_t *, uint32_t *, const uint8_t *);
#endif

#ifdef TEST_COMPUTE_ROOT
extern void compute_root_jazz(unsigned char *root, uint32_t addr[8], const unsigned char *leaf, unsigned long leaf_idx,
                              const unsigned char *auth_path, const unsigned char *pub_seed);
#endif

#ifdef TEST_HASH_MESSAGE
extern void hash_message_jazz(uint8_t *, const uint8_t *, const uint8_t *, uint64_t, const uint8_t *, size_t);
#endif

/**
 * Computes a leaf node from a WOTS public key using an L-tree.
 * Note that this destroys the used WOTS public key.
 */
void l_tree(const xmss_params *params, unsigned char *leaf, unsigned char *wots_pk, const unsigned char *pub_seed,
            uint32_t addr[8]) {
    unsigned int l = params->wots_len;
    unsigned int parent_nodes;
    uint32_t i;
    uint32_t height = 0;

    set_tree_height(addr, height);

    while (l > 1) {
        parent_nodes = l >> 1;
        for (i = 0; i < parent_nodes; i++) {
            set_tree_index(addr, i);
            /* Hashes the nodes at (i*2)*params->n and (i*2)*params->n + 1 */
            thash_h(params, wots_pk + i * params->n, wots_pk + (i * 2) * params->n, pub_seed, addr);
        }
        /* If the row contained an odd number of nodes, the last node was not
           hashed. Instead, we pull it up to the next layer. */
        if (l & 1) {
            memcpy(wots_pk + (l >> 1) * params->n, wots_pk + (l - 1) * params->n, params->n);
            l = (l >> 1) + 1;
        } else {
            l = l >> 1;
        }
        height++;
        set_tree_height(addr, height);
    }
    memcpy(leaf, wots_pk, params->n);
}

/**
 * Computes a root node given a leaf and an auth path
 */
void compute_root(const xmss_params *params, unsigned char *root, const unsigned char *leaf, unsigned long leafidx,
                  const unsigned char *auth_path, const unsigned char *pub_seed, uint32_t addr[8]) {
    uint32_t i;
    unsigned char buffer[2 * params->n];

    /* If leafidx is odd (last bit = 1), current path element is a right child
       and auth_path has to go left. Otherwise it is the other way around. */
    if (leafidx & 1) {
        memcpy(buffer + params->n, leaf, params->n);
        memcpy(buffer, auth_path, params->n);
    } else {
        memcpy(buffer, leaf, params->n);
        memcpy(buffer + params->n, auth_path, params->n);
    }
    auth_path += params->n;

    for (i = 0; i < params->tree_height - 1; i++) {
        set_tree_height(addr, i);
        leafidx >>= 1;
        set_tree_index(addr, leafidx);

        /* Pick the right or left neighbor, depending on parity of the node. */
        if (leafidx & 1) {
#ifdef TEST_THASH_H
            // NOTE: in the jasmin impl, addr is the 2nd argument because writable ptrs must come first in the arguments
            thash_h_jazz(buffer + params->n, addr, buffer, pub_seed);
#else
            thash_h(params, buffer + params->n, buffer, pub_seed, addr);
#endif

            memcpy(buffer, auth_path, params->n);
        } else {
#ifdef TEST_THASH_H
            // NOTE: in the jasmin impl, addr is the 2nd argument because writable ptrs must come first in the arguments
            thash_h_jazz(buffer, addr, buffer, pub_seed);
#else
            thash_h(params, buffer, buffer, pub_seed, addr);
#endif
            memcpy(buffer + params->n, auth_path, params->n);
        }

        auth_path += params->n;
    }

    /* The last iteration is exceptional; we do not copy an auth_path node. */
    set_tree_height(addr, params->tree_height - 1);
    leafidx >>= 1;
    set_tree_index(addr, leafidx);

#ifdef TEST_THASH_H
    // NOTE: in the jasmin impl, addr is the 2nd argument because writable ptrs must come first in the arguments
    thash_h_jazz(root, addr, buffer, pub_seed);
#else
    thash_h(params, root, buffer, pub_seed, addr);
#endif
}

/**
 * Computes the leaf at a given address. First generates the WOTS key pair,
 * then computes leaf using l_tree. As this happens position independent, we
 * only require that addr encodes the right ltree-address.
 */
void gen_leaf_wots(const xmss_params *params, unsigned char *leaf, const unsigned char *sk_seed,
                   const unsigned char *pub_seed, uint32_t ltree_addr[8], uint32_t ots_addr[8]) {
    unsigned char pk[params->wots_sig_bytes];

    wots_pkgen(params, pk, sk_seed, pub_seed, ots_addr);

#ifdef TEST_LTREE
    // NOTE: The addr is before pub_seed in the jasmin impl because the writable ptrs must come first
    // in the list of arguments
    l_tree_jazz(leaf, pk, ltree_addr, pub_seed);
#else
    l_tree(params, leaf, pk, pub_seed, ltree_addr);
#endif
}

/**
 * Verifies a given message signature pair under a given public key.
 * Note that this assumes a pk without an OID, i.e. [root || PUB_SEED]
 */
int xmss_core_sign_open(const xmss_params *params, unsigned char *m, unsigned long long *mlen, const unsigned char *sm,
                        unsigned long long smlen, const unsigned char *pk) {
    /* XMSS signatures are fundamentally an instance of XMSSMT signatures.
       For d=1, as is the case with XMSS, some of the calls in the XMSSMT
       routine become vacuous (i.e. the loop only iterates once, and address
       management can be simplified a bit).*/
    return xmssmt_core_sign_open(params, m, mlen, sm, smlen, pk);
}

/**
 * Verifies a given message signature pair under a given public key.
 * Note that this assumes a pk without an OID, i.e. [root || PUB_SEED]
 */
int xmssmt_core_sign_open(const xmss_params *params, unsigned char *m, unsigned long long *mlen,
                          const unsigned char *sm, unsigned long long smlen, const unsigned char *pk) {
    const unsigned char *pub_root = pk;
    const unsigned char *pub_seed = pk + params->n;
    unsigned char wots_pk[params->wots_sig_bytes];
    unsigned char leaf[params->n];
    unsigned char root[params->n];
    unsigned char *mhash = root;
    unsigned long long idx = 0;
    unsigned int i;
    uint32_t idx_leaf;

    uint32_t ots_addr[8] = {0};
    uint32_t ltree_addr[8] = {0};
    uint32_t node_addr[8] = {0};

    set_type(ots_addr, XMSS_ADDR_TYPE_OTS);
    set_type(ltree_addr, XMSS_ADDR_TYPE_LTREE);
    set_type(node_addr, XMSS_ADDR_TYPE_HASHTREE);

    *mlen = smlen - params->sig_bytes;

    /* Convert the index bytes from the signature to an integer. */
    idx = bytes_to_ull(sm, params->index_bytes);

    /* Put the message all the way at the end of the m buffer, so that we can
     * prepend the required other inputs for the hash function. */
    memcpy(m + params->sig_bytes, sm + params->sig_bytes, *mlen);

/* Compute the message hash. */
#ifdef TEST_HASH_MESSAGE
    hash_message_jazz(mhash, sm + params->index_bytes, pk, idx,
                      m + params->sig_bytes - params->padding_len - 3 * params->n, *mlen);
#else
    hash_message(params, mhash, sm + params->index_bytes, pk, idx,
                 m + params->sig_bytes - params->padding_len - 3 * params->n, *mlen);
#endif

    sm += params->index_bytes + params->n;

    /* For each subtree.. */
    for (i = 0; i < params->d; i++) {
        idx_leaf = (idx & ((1 << params->tree_height) - 1));
        idx = idx >> params->tree_height;

        set_layer_addr(ots_addr, i);
        set_layer_addr(ltree_addr, i);
        set_layer_addr(node_addr, i);

        set_tree_addr(ltree_addr, idx);
        set_tree_addr(ots_addr, idx);
        set_tree_addr(node_addr, idx);

        /* The WOTS public key is only correct if the signature was correct. */
        set_ots_addr(ots_addr, idx_leaf);
        /* Initially, root = mhash, but on subsequent iterations it is the root
           of the subtree below the currently processed subtree. */
        wots_pk_from_sig(params, wots_pk, sm, root, pub_seed, ots_addr);
        sm += params->wots_sig_bytes;

        /* Compute the leaf node using the WOTS public key. */
        set_ltree_addr(ltree_addr, idx_leaf);
        l_tree(params, leaf, wots_pk, pub_seed, ltree_addr);

/* Compute the root node of this subtree. */
#ifdef TEST_COMPUTE_ROOT
        // NOTE: The addr is the 2nd argument in the jasmin impl because the writable ptrs must come first
        // in the list of arguments
        compute_root_jazz(root, node_addr, leaf, idx_leaf, sm, pub_seed);
#else
        compute_root(params, root, leaf, idx_leaf, sm, pub_seed, node_addr);
#endif

        sm += params->tree_height * params->n;
    }

    /* Check if the root node equals the root node in the public key. */
    if (memcmp(root, pub_root, params->n)) {
        /* If not, zero the message */
        memset(m, 0, *mlen);
        *mlen = 0;
        return -1;
    }

    /* If verification was successful, copy the message from the signature. */
    memcpy(m, sm, *mlen);

    return 0;
}
