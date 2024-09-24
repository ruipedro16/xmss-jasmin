pragma Goals : printall.

require import AllCore List RealExp IntDiv Distr DList.

from Jasmin require import JModel.

require import Params Address Hash WOTS LTree XMSS_MT_TreeHash.

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

  proc rootFromSig(idx_sig : W32.t, sig_ots : wots_signature, auth : auth_path, M : nbytes, 
                   _seed : seed, address : adrs) : nbytes = {
    var pk_ots : wots_pk;
    var nodes0, nodes1 : nbytes;
    
    address <- set_type address 0;
    address <- set_ots_addr address (W32.to_uint idx_sig);

    pk_ots <@ WOTS.pkFromSig(M, sig_ots, _seed, address);

    address <- set_type address 1;
    address <- set_ltree_addr address (W32.to_uint idx_sig);

    nodes0 <@ LTree.ltree(pk_ots, address, _seed);

    address <- set_type address 2;
    address <- set_tree_index address (W32.to_uint idx_sig);

    nodes0 <@ rootFromSigInnerLoop (nodes0, idx_sig, _seed, auth, address);

    return nodes0;
  }
}.

equiv rootFromSigHop : 
    RootFromSig_Hop.rootFromSig ~ RootFromSig.rootFromSig : ={arg} ==> ={res}.
proof.
proc.
inline {1} RootFromSig_Hop.rootFromSigInnerLoop.
sim => />.
qed.

