#include <assert.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "hash.h"
#include "macros.h"
#include "params.h"
#include "print.h"
#include "randombytes.h"
#include "wots.h"
#include "xmss.h"

#ifndef IMPL
#error IMPL not defined
#endif

#ifndef MAX_MLEN
#define MAX_MLEN 128
#endif

#ifndef TESTS
#define TESTS 10000
#endif

#define XMSS_N p.n

extern void addr_to_bytes_jazz(uint8_t *, const uint32_t *);
extern void prf_jazz(uint8_t *, const uint8_t *, const uint8_t *);
extern void prf_keygen_jazz(uint8_t *, const uint8_t *, const uint8_t *);
extern void hash_message_jazz(uint8_t *, const uint8_t *, const uint8_t *, uint64_t, uint8_t *, size_t);
extern void thash_h_jazz(uint8_t *, uint32_t *, const uint8_t *, const uint8_t *);
extern void thash_f_jazz(uint8_t *, uint32_t *, const uint8_t *);

void test_addr_to_bytes(void) {
    uint32_t addr[8];
    uint8_t addr_as_bytes_ref[32], addr_as_bytes_jazz[32];

    for (int i = 0; i < TESTS; i++) {
        randombytes((uint8_t *)addr, 8 * sizeof(uint32_t));

        addr_to_bytes_jazz(addr_as_bytes_jazz, addr);
        addr_to_bytes(addr_as_bytes_ref, addr);

        if (memcmp(addr_as_bytes_ref, addr_as_bytes_jazz, 32 * sizeof(uint8_t)) != 0) {
            print_str_u8("Ref", addr_as_bytes_ref, 32 * sizeof(uint8_t));
            print_str_u8("Jazz", addr_as_bytes_jazz, 32 * sizeof(uint8_t));
        }

        assert(memcmp(addr_as_bytes_ref, addr_as_bytes_jazz, 32 * sizeof(uint8_t)) == 0);
    }

    puts("addr to bytes: OK");
}

void test_prf(void) {
    bool debug = false;

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

    uint8_t out_ref[p.n], out_jazz[p.n];
    uint8_t in[32];
    uint8_t key[p.n];

    for (int i = 0; i < TESTS; i++) {
        if (debug) {
            printf("[prf] Test %d/%d\n", i, TESTS);
        }

        memset(out_ref, 0, p.n * sizeof(uint8_t));
        memset(out_jazz, 0, p.n * sizeof(uint8_t));

        randombytes(in, 32 * sizeof(uint8_t));
        randombytes(key, p.n * sizeof(uint8_t));

        prf(&p, out_ref, in, key);
        prf_jazz(out_jazz, in, key);

        if (memcmp(out_ref, out_jazz, p.n * sizeof(uint8_t)) != 0) {
            print_str_u8("out ref", out_ref, p.n * sizeof(uint8_t));
            print_str_u8("out jazz", out_jazz, p.n * sizeof(uint8_t));
        }

        assert(memcmp(out_ref, out_jazz, p.n * sizeof(uint8_t)) == 0);
    }

    puts("prf: OK");
}

void test_prf_keygen(void) {
    bool debug = false;

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

    uint8_t out_ref[p.n], out_jazz[p.n];
    uint8_t in[p.n + 32];
    uint8_t key[p.n];

    for (int i = 0; i < TESTS; i++) {
        if (debug) {
            printf("[prf_keygen] Test %d/%d\n", i, TESTS);
        }

        memset(out_ref, 0, p.n * sizeof(uint8_t));
        memset(out_jazz, 0, p.n * sizeof(uint8_t));

        randombytes(in, (p.n + 32) * sizeof(uint8_t));
        randombytes(key, p.n * sizeof(uint8_t));

        prf_keygen(&p, out_ref, in, key);
        prf_keygen_jazz(out_jazz, in, key);

        if (memcmp(out_ref, out_jazz, p.n * sizeof(uint8_t)) != 0) {
            print_str_u8("out ref", out_ref, p.n * sizeof(uint8_t));
            print_str_u8("out jazz", out_jazz, p.n * sizeof(uint8_t));
        }

        assert(memcmp(out_ref, out_jazz, p.n * sizeof(uint8_t)) == 0);
    }

    puts("prf keygen: OK");
}

void test_hash_message(void) {
    bool debug = false;

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

    uint8_t hash_ref[p.n], hash_jazz[p.n];
    uint8_t randomness[p.n];
    uint8_t root[p.n];
    uint64_t idx;
    uint8_t msg_ref[MAX_MLEN], msg_jazz[MAX_MLEN];

    for (int i = 0; i < TESTS; i++) {
        for (size_t inlen = 1; inlen < MAX_MLEN; inlen++) {
            if (debug) {
                printf("[hash message (inlen=%ld)] Test %d/%d\n", inlen, i, TESTS);
            }

            randombytes(randomness, p.n);
            randombytes(root, p.n);
            randombytes((uint8_t *)&idx, sizeof(uint64_t));

            randombytes(msg_ref, inlen);
            memcpy(msg_jazz, msg_ref, inlen);

            hash_message_jazz(hash_jazz, randomness, root, idx, msg_jazz, inlen);
            hash_message(&p, hash_ref, randomness, root, idx, msg_ref, inlen);

            // TODO: Asserts
        }
    }

    puts("hash message: OK");
}

void test_thash_h(void) {
    bool debug = false;

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

    uint8_t out_ref[XMSS_N], out_jazz[XMSS_N];
    uint8_t in[2 * XMSS_N];
    uint8_t pub_seed[XMSS_N];
    uint32_t addr_ref[8], addr_jazz[8];

    for (int i = 0; i < TESTS; i++) {
        if (debug) {
            printf("[THASH H] Test %d/%d\n", i, TESTS);
        }

        randombytes(out_ref, XMSS_N);
        memcpy(out_jazz, out_ref, XMSS_N);
        randombytes(in, 2 * XMSS_N);
        randombytes(pub_seed, XMSS_N);
        randombytes((uint8_t *)addr_ref, 8 * sizeof(uint32_t));
        memcpy(addr_jazz, addr_ref, 8 * sizeof(uint32_t));

        assert(memcmp(addr_jazz, addr_ref, 8 * sizeof(uint32_t)) == 0);

        thash_h(&p, out_ref, in, pub_seed, addr_ref);
        thash_h_jazz(out_jazz, addr_jazz, in, pub_seed);

        if (memcmp(out_ref, out_jazz, XMSS_N) != 0) {
            print_str_u8("out ref", out_ref, XMSS_N);
            print_str_u8("out jazz", out_jazz, XMSS_N);
        }

        assert(memcmp(out_ref, out_jazz, XMSS_N) == 0);
        assert(memcmp(addr_jazz, addr_ref, 8 * sizeof(uint32_t)) == 0);
    }

    puts("thash_h: OK");
}

void test_thash_f(void) {
    bool debug = false;

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

    uint8_t out_ref[XMSS_N], out_jazz[XMSS_N];
    uint8_t pub_seed[XMSS_N];
    uint32_t addr_ref[8], addr_jazz[8];

    for (int i = 0; i < TESTS; i++) {
        if (debug) {
            printf("[THASH F] Test %d/%d\n", i, TESTS);
        }

        randombytes(out_ref, XMSS_N);
        memcpy(out_jazz, out_ref, XMSS_N);
        randombytes(pub_seed, XMSS_N);
        randombytes((uint8_t *)addr_ref, 8 * sizeof(uint32_t));
        memcpy(addr_jazz, addr_ref, 8 * sizeof(uint32_t));

        assert(memcmp(addr_jazz, addr_ref, 8 * sizeof(uint32_t)) == 0);

        thash_f(&p, out_ref, out_ref, pub_seed, addr_ref);
        thash_f_jazz(out_jazz, addr_jazz, pub_seed);

        assert(memcmp(out_ref, out_jazz, XMSS_N) == 0);
        assert(memcmp(addr_ref, addr_jazz, 8 * sizeof(uint32_t)) == 0);
    }

    puts("thash_f: OK");
}

void test_wots(void) {
    bool debug = false;

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

    // C functions replaced by corresponding Jasmin functions:
    // [X] thash_f_jazz
    // [X] prf_keygen_jazz

    for (int i = 0; i < TESTS; i++) {
        if (debug) {
            printf("[WOTS signature and PK derivation] Test %d/%d\n", i, TESTS);
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

    puts("WOTS: OK");
}

void test_api(void) {
    bool debug = false;

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

    // C functions replaced by corresponding Jasmin functions:
    //
    //

    unsigned char pk[XMSS_OID_LEN + p.pk_bytes];
    unsigned char sk[XMSS_OID_LEN + p.sk_bytes];

    unsigned char m[MAX_MLEN];
    unsigned char sm[p.sig_bytes + MAX_MLEN];
    unsigned char mout[p.sig_bytes + MAX_MLEN];
    unsigned long long smlen;
    unsigned long long mlen = MAX_MLEN;

    for (int i = 0; i < 5; i++) {
        if (debug) {
            printf("[XMSS sign+verify] Test %d/%d\n", i, TESTS);
        }

        xmss_keypair(pk, sk, oid);
        randombytes(m, MAX_MLEN);
        xmss_sign(sk, sm, &smlen, m, MAX_MLEN);
        int res = xmss_sign_open(mout, &mlen, sm, smlen, pk);
        assert(res == 0);
    }
    puts("XMSS: OK");
}

int main(void) {
    printf("HASH: Running tests for [%s]\n", xstr(IMPL));
    test_addr_to_bytes();
    test_prf();
    test_prf_keygen();
    test_thash_h();
    test_thash_f();
    // TODO:: Test Message
    test_wots();  // Wots but replaces all C [hash] functions with the respective Jasmin function
    test_api();   // Same as before but for XMSS
    printf("[%s]: Hash OK\n\n", xstr(IMPL));
    return 0;
}
