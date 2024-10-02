pragma Goals : printall.

require import AllCore List RealExp IntDiv Distr DList.

from Jasmin require import JModel.

require import Params Address Hash WOTS LTree XMSS_MT_TreeHash.
require import XMSS_IMPL Parameters.
require import Repr2.

require import Array32 Array64.

require import Correctness_Mem.

module RootFromSig_Hop = {
  proc rootFromSigInnerLoop (nodes0 : nbytes, idx_sig : W32.t, _seed : seed, auth : auth_path, address : adrs) : nbytes = {
    var k : int;
    var nodes1 : nbytes;
    var index : int;
    var auth_k : nbytes;

    k <- 0;
    while (k < h) {
      address <- set_tree_height address k;

      if (floor ((W32.to_uint idx_sig)%r / (2^k)%r) %% 2 = 0) {
        index <- get_tree_index address;
        address <- set_tree_index address (index %/ 2);

        auth_k <- nth witness (val auth) k;
        nodes1 <@ Hash.rand_hash (nodes0, auth_k, _seed, address);
      } else {
        index <- get_tree_index address;
        address <- set_tree_index address ((index - 1) %/ 2);

        auth_k <- nth witness (val auth) k;
        nodes1 <@ Hash.rand_hash (auth_k, nodes0, _seed, address);
      }

      nodes0 <- nodes1;
      k <- k + 1;
    }

    return nodes0;
  } 
}.

