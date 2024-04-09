#include <assert.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "macros.h"
#include "params.h"
#include "print.h"
#include "randombytes.h"
#include "wots.h"

#ifndef IMPL
#error IMPL not defined
#endif

#ifndef TESTS
#define TESTS 1000
#endif

#define XMSS_N p.n
#define XMSS_WOTS_LEN p.wots_len

extern void wots_pkgen_jazz(uint8_t *, const uint8_t *, const uint8_t *, uint32_t *);
extern void wots_sign_jazz(uint8_t *, const uint8_t *, const uint8_t *, const uint8_t *, uint32_t *);
extern void wots_pk_from_sig_jazz(uint8_t *pk, const uint8_t *sig, const uint8_t *msg, const uint8_t *pub_seed,
                                  uint32_t *);

void test_wots(void) {
    // Same test as reference implementation
    bool debug = true;

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

    uint8_t seed[p.n];
    uint8_t pub_seed[p.n];
    uint8_t pk1[p.wots_sig_bytes];
    uint8_t pk2[p.wots_sig_bytes];
    uint8_t sig[p.wots_sig_bytes];
    uint8_t m[p.n];
    uint32_t addr[8] = {0};

    // C functions replaced by corresponding Jasmin functions
    // [X] expand seed
    // [X] wots checksum
    // [X] gen chain

    for (int i = 0; i < TESTS; i++) {
        if (debug) {
            printf("[WOTS signature and PK derivation] Test %d/%d\n", i + 1, TESTS);
        }

        randombytes(seed, p.n);
        randombytes(pub_seed, p.n);
        randombytes(m, p.n);
        randombytes((uint8_t *)addr, 8 * sizeof(uint32_t));

        wots_pkgen(&p, pk1, seed, pub_seed, addr);
        wots_sign(&p, sig, m, seed, pub_seed, addr);
        wots_pk_from_sig(&p, pk2, sig, m, pub_seed, addr);

        assert(memcmp(pk1, pk2, p.wots_sig_bytes) == 0);
    }
}

void test_wots_pkgen(void) {
    bool debug = true;

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

    uint8_t seed[p.n];
    uint8_t pub_seed[p.n];
    uint8_t pk_ref[p.wots_sig_bytes];
    uint8_t pk_jazz[p.wots_sig_bytes];
    uint32_t addr_ref[8] = {0};
    uint32_t addr_jazz[8] = {0};

    for (int i = 0; i < TESTS; i++) {
        if (debug) {
            printf("[WOTS PK Gen] Test %d/%d\n", i + 1, TESTS);
        }

        memset(pk_ref, 0, p.wots_sig_bytes);
        memset(pk_jazz, 0, p.wots_sig_bytes);

        randombytes(seed, p.n);
        randombytes(pub_seed, p.n);
        randombytes((uint8_t *)addr_ref, 8 * sizeof(uint32_t));
        memcpy(addr_jazz, addr_ref, 8 * sizeof(uint32_t));

        wots_pkgen(&p, pk_ref, seed, pub_seed, addr_ref);
        wots_pkgen_jazz(pk_jazz, seed, pub_seed, addr_jazz);

        if (memcmp(pk_ref, pk_jazz, p.wots_sig_bytes) != 0) {
            print_str_u8("pk ref", pk_ref, p.wots_sig_bytes);
            print_str_u8("pk jazz", pk_jazz, p.wots_sig_bytes);
        }

        assert(memcmp(pk_ref, pk_jazz, p.wots_sig_bytes) == 0);
    }
}

void test_wots_sign(void) {
    bool debug = true;

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

    uint8_t seed[p.n];
    uint8_t pub_seed[p.n];
    uint8_t pk[p.wots_sig_bytes];
    uint8_t sig_ref[p.wots_sig_bytes];
    uint8_t sig_jazz[p.wots_sig_bytes];
    uint8_t m[p.n];
    uint32_t addr_ref[8] = {0};
    uint32_t addr_jazz[8] = {0};

    for (int i = 0; i < TESTS; i++) {
        if (debug) {
            printf("[WOTS Sign] Test %d/%d\n", i + 1, TESTS);
        }

        randombytes(seed, p.n);
        randombytes(pub_seed, p.n);
        randombytes(m, p.n);
        randombytes((uint8_t *)addr_ref, 8 * sizeof(uint32_t));
        memcpy(addr_jazz, addr_ref, 8 * sizeof(uint32_t));

        // generate a wots pk
        wots_pkgen(&p, pk, seed, pub_seed, addr_ref);

        // sign
        wots_sign(&p, sig_ref, m, seed, pub_seed, addr_ref);
        wots_sign_jazz(sig_jazz, m, seed, pub_seed, addr_jazz);

        assert(memcmp(sig_ref, sig_jazz, p.wots_sig_bytes) == 0);
    }
}

void test_wots_pk_from_sig(void) {
    bool debug = true;

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

    uint8_t seed[p.n];
    uint8_t pub_seed[p.n];
    uint8_t pk_ref[p.wots_sig_bytes];
    uint8_t pk_jazz[p.wots_sig_bytes];
    uint8_t sig[p.wots_sig_bytes];
    uint8_t m[p.n];
    uint32_t addr_ref[8] = {0};
    uint32_t addr_jazz[8] = {0};

    for (int i = 0; i < TESTS; i++) {
        if (debug) {
            printf("[WOTS PK from SIG] Test %d/%d\n", i + 1, TESTS);
        }

        randombytes(seed, p.n);
        randombytes(pub_seed, p.n);
        randombytes(m, p.n);
        randombytes((uint8_t *)addr_ref, 8 * sizeof(uint32_t));

        // Generate a public key and sign
        wots_pkgen(&p, pk_ref, seed, pub_seed, addr_ref);
        wots_sign(&p, sig, m, seed, pub_seed, addr_ref);

        memcpy(addr_jazz, addr_ref, 8 * sizeof(uint32_t));
        assert(memcmp(addr_jazz, addr_ref, 8 * sizeof(uint32_t)) == 0);

        wots_pk_from_sig(&p, pk_ref, sig, m, pub_seed, addr_ref);
        wots_pk_from_sig_jazz(pk_jazz, sig, m, pub_seed, addr_jazz);

        assert(memcmp(pk_ref, pk_jazz, p.wots_sig_bytes) == 0);
    }
}

void test_wots_jazz(void) {
    bool debug = true;

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

    uint8_t seed[p.n];
    uint8_t pub_seed[p.n];
    uint8_t pk1[p.wots_sig_bytes];
    uint8_t pk2[p.wots_sig_bytes];
    uint8_t sig[p.wots_sig_bytes];
    uint8_t m[p.n];
    uint32_t addr[8] = {0};

    for (int i = 0; i < TESTS; i++) {
        if (debug) {
            printf("[WOTS JAZZ] Test %d/%d\n", i + 1, TESTS);
        }

        randombytes(seed, p.n);
        randombytes(pub_seed, p.n);
        randombytes(m, p.n);
        randombytes((uint8_t *)addr, 8 * sizeof(uint32_t));

        wots_pkgen_jazz(pk1, seed, pub_seed, addr);
        wots_sign_jazz(sig, m, seed, pub_seed, addr);
        wots_pk_from_sig_jazz(pk2, sig, m, pub_seed, addr);

        assert(memcmp(pk1, pk2, p.wots_sig_bytes) == 0);
    }
}

int main(void) {
    test_wots();
    test_wots_pkgen();
    test_wots_sign();
    test_wots_pk_from_sig();
    test_wots_jazz();
    printf("[%s]: WOTS OK\n", xstr(IMPL));
    return 0;
}
