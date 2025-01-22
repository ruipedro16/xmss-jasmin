#include "params.h"

void treehash_new(const xmss_params *params, unsigned char *root, const unsigned char *sk_seed,
                  const unsigned char *pub_seed, uint32_t leaf_idx, /* leaf_idx in the old impl */
                  uint32_t target_height, const uint32_t subtree_addr[8]);

void build_auth_path(const xmss_params *params,
                     uint8_t *auth_path,  // size XMSS_TREE_HEIGHT * XMSS_N
                     const unsigned char *sk_seed, const unsigned char *pub_seed,
                     uint32_t i,  // wots+ Key pair index (index of the node on the tree)
                     uint32_t *addr);

void treesig(const xmss_params *params, unsigned char *sig, const unsigned char *M, unsigned char *sk, uint32_t idx_sig,
             uint32_t *addr);

int xmssmt_core_seed_keypair_new(const xmss_params *params, unsigned char *pk, unsigned char *sk,
                                 const unsigned char *seed);

int xmssmt_core_sign_new(const xmss_params *params, unsigned char *sk, unsigned char *sm, unsigned long long *smlen,
                         const unsigned char *m, unsigned long long mlen);

void new_compute_root(const xmss_params *params, unsigned char *root, const unsigned char *leaf, unsigned long leafidx,
                      const unsigned char *auth_path, const unsigned char *pub_seed, uint32_t addr[8]);