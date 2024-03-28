#include "wots.h"

#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "hash.h"
#include "hash_address.h"
#include "params.h"
#include "utils.h"

#ifdef TEST_EXPAND_SEED
extern void expand_seed_jazz(uint8_t *, const uint8_t *, const uint8_t *, uint32_t *);
#endif

#ifdef TEST_GEN_CHAIN
extern void gen_chain_jazz(uint8_t *, const uint8_t *, uint32_t, uint32_t, const uint8_t *, uint32_t *);
#endif

#ifdef TEST_GEN_CHAIN_INPLACE
extern void gen_chain_inplace_jazz(uint8_t *, const uint8_t *, uint32_t, uint32_t, const uint8_t *, uint32_t *);
#endif

#ifdef TEST_WOTS_CHECKSUM
extern void wots_checksum_jazz(int *, const int *);
#endif

/**
 * Helper method for pseudorandom key generation.
 * Expands an n-byte array into a len*n byte array using the `prf_keygen` function.
 */
void expand_seed(const xmss_params *params, unsigned char *outseeds, const unsigned char *inseed,
                 const unsigned char *pub_seed, uint32_t addr[8]) {
    uint32_t i;
    unsigned char buf[params->n + 32];

    set_hash_addr(addr, 0);
    set_key_and_mask(addr, 0);
    memcpy(buf, pub_seed, params->n);
    for (i = 0; i < params->wots_len; i++) {
        set_chain_addr(addr, i);
        addr_to_bytes(buf + params->n, addr);
        prf_keygen(params, outseeds + i * params->n, buf, inseed);
    }
}

/**
 * Computes the chaining function.
 * out and in have to be n-byte arrays.
 *
 * Interprets in as start-th value of the chain.
 * addr has to contain the address of the chain.
 */
static void gen_chain(const xmss_params *params, unsigned char *out, const unsigned char *in, unsigned int start,
                      unsigned int steps, const unsigned char *pub_seed, uint32_t addr[8]) {
    uint32_t i;

    /* Initialize out with the value at position 'start'. */
    memcpy(out, in, params->n);

    /* Iterate 'steps' calls to the hash function. */
    for (i = start; i < (start + steps) && i < params->wots_w; i++) {
        set_hash_addr(addr, i);
        thash_f(params, out, out, pub_seed, addr);
    }
}

/**
 * base_w algorithm as described in draft.
 * Interprets an array of bytes as integers in base w.
 * This only works when log_w is a divisor of 8.
 */
static void base_w(const xmss_params *params, int *output, const int out_len, const unsigned char *input) {
    int in = 0;
    int out = 0;
    unsigned char total;
    int bits = 0;
    int consumed;

    for (consumed = 0; consumed < out_len; consumed++) {
        if (bits == 0) {
            total = input[in];
            in++;
            bits += 8;
        }
        bits -= params->wots_log_w;
        output[out] = (total >> bits) & (params->wots_w - 1);
        out++;
    }
}

/* Computes the WOTS+ checksum over a message (in base_w). */
static void wots_checksum(const xmss_params *params, int *csum_base_w, const int *msg_base_w) {
    int csum = 0;
    unsigned char csum_bytes[(params->wots_len2 * params->wots_log_w + 7) / 8];
    unsigned int i;

    /* Compute checksum. */
    for (i = 0; i < params->wots_len1; i++) {
        csum += params->wots_w - 1 - msg_base_w[i];
    }

    /* Convert checksum to base_w. */
    /* Make sure expected empty zero bits are the least significant bits. */
    csum = csum << (8 - ((params->wots_len2 * params->wots_log_w) % 8));
    ull_to_bytes(csum_bytes, sizeof(csum_bytes), csum);
    base_w(params, csum_base_w, params->wots_len2, csum_bytes);
}

/* Takes a message and derives the matching chain lengths. */
static void chain_lengths(const xmss_params *params, int *lengths, const unsigned char *msg) {
    base_w(params, lengths, params->wots_len1, msg);
#ifdef TEST_WOTS_CHECKSUM
    wots_checksum_jazz(lengths + params->wots_len1, lengths);
#else
    wots_checksum(params, lengths + params->wots_len1, lengths);
#endif
}

/**
 * WOTS key generation. Takes a 32 byte seed for the private key, expands it to
 * a full WOTS private key and computes the corresponding public key.
 * It requires the seed pub_seed (used to generate bitmasks and hash keys)
 * and the address of this WOTS key pair.
 *
 * Writes the computed public key to 'pk'.
 */
void wots_pkgen(const xmss_params *params, unsigned char *pk, const unsigned char *seed, const unsigned char *pub_seed,
                uint32_t addr[8]) {
    uint32_t i;

/* The WOTS+ private key is derived from the seed. */
#ifdef TEST_EXPAND_SEED
    expand_seed_jazz(pk, seed, pub_seed, addr);
#else
    expand_seed(params, pk, seed, pub_seed, addr);
#endif

    for (i = 0; i < params->wots_len; i++) {
        set_chain_addr(addr, i);

// TODO: run regular gen chain if gen chain inplace is not defined
#ifdef TEST_GEN_CHAIN_INPLACE
        gen_chain_inplace_jazz(pk + i * params->n, pk + i * params->n, 0, params->wots_w - 1, pub_seed, addr);
#else
        gen_chain(params, pk + i * params->n, pk + i * params->n, 0, params->wots_w - 1, pub_seed, addr);
#endif
    }
}

/**
 * Takes a n-byte message and the 32-byte seed for the private key to compute a
 * signature that is placed at 'sig'.
 */
void wots_sign(const xmss_params *params, unsigned char *sig, const unsigned char *msg, const unsigned char *seed,
               const unsigned char *pub_seed, uint32_t addr[8]) {
    int lengths[params->wots_len];
    uint32_t i;

    chain_lengths(params, lengths, msg);

/* The WOTS+ private key is derived from the seed. */
#ifdef TEST_EXPAND_SEED
    expand_seed_jazz(sig, seed, pub_seed, addr);
#else
    expand_seed(params, sig, seed, pub_seed, addr);
#endif

    for (i = 0; i < params->wots_len; i++) {
        set_chain_addr(addr, i);

// TODO: run regular gen chain if gen chain inplace is not defined
#ifdef TEST_GEN_CHAIN
        gen_chain_inplace_jazz(sig + i * params->n, sig + i * params->n, 0, lengths[i], pub_seed, addr);
#else
        gen_chain(params, sig + i * params->n, sig + i * params->n, 0, lengths[i], pub_seed, addr);
#endif
    }
}

/**
 * Takes a WOTS signature and an n-byte message, computes a WOTS public key.
 *
 * Writes the computed public key to 'pk'.
 */
void wots_pk_from_sig(const xmss_params *params, unsigned char *pk, const unsigned char *sig, const unsigned char *msg,
                      const unsigned char *pub_seed, uint32_t addr[8]) {
    int lengths[params->wots_len];
    uint32_t i;

    chain_lengths(params, lengths, msg);

    for (i = 0; i < params->wots_len; i++) {
        set_chain_addr(addr, i);

#ifdef TEST_GEN_CHAIN
        gen_chain_jazz(pk + i * params->n, sig + i * params->n, lengths[i], params->wots_w - 1 - lengths[i], pub_seed,
                       addr);
#else
        gen_chain(params, pk + i * params->n, sig + i * params->n, lengths[i], params->wots_w - 1 - lengths[i],
                  pub_seed, addr);
#endif
    }
}
