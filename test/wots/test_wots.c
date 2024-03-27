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
    // [X] gen chain
    // [ ] wots checksum

    for (int i = 0; i < TESTS; i++) {
        if (debug) {
            printf("[WOTS signature and PK derivation] Test %d/%d\n", i, TESTS);
        }

        randombytes(seed, p.n);
        randombytes(pub_seed, p.n);
        randombytes(m, p.n);
        randombytes((unsigned char *)addr, 8 * sizeof(uint32_t));

        // TODO: Replace by the corresponding jasmin functions
        wots_pkgen(&p, pk1, seed, pub_seed, addr);
        wots_sign(&p, sig, m, seed, pub_seed, addr);
        wots_pk_from_sig(&p, pk2, sig, m, pub_seed, addr);

        assert(memcmp(pk1, pk2, p.wots_sig_bytes) == 0);
    }
}

int main(void) {
    test_wots();         // NOT IMPLEMENTED YET
    printf("WOTS OK\n");
    return 0;
}