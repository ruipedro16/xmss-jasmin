pragma Goals : printall.


require import AllCore List RealExp IntDiv Distr DList.
require (*--*) Subtype. 

from Jasmin require import JModel.
 
require import XMSS_MT_Types Address Hash LTree WOTS.
import XMSS_MT_Params Params.

(**********************************************************************************************)

(* It is REQUIRED that s % 2^t = 0, i.e., that the leaf at index s is a leftmost leaf of a sub-tree of height t. *)
pred leftmost_leaf (s t : int)  = s %% 2^t = 0.

(* Precondition *)
pred treehash_p (s t : int) = s %% (1 `<<` t) <> 0.


(* NOTE: In the Jasmin implementation, treehash (in xmss_core.c) computes both the authentication 
         path and the resulting root node *)
(* computation of the internal n-byte nodes of a Merkle tree *)
(* The treeHash algorithm returns the root node of a tree of height t with the leftmost 
   leaf being the hash of the WOTS+ pk with index s.  
*)
module TreeHash = {
  (* Computes the root *)
  proc treehash(pub_seed sk_seed : seed, s t : int, address : adrs) : nbytes * adrs = {
    var node : nbytes;
    var stack : nbytes list <- nseq ((h %/ d) + 1) (NBytes.insubd (nseq n W8.zero));
    var pk : wots_pk;
    var offset : int;
    var i, j : int;
    var tree_index : int;
    var top_node : nbytes;

    offset <- 0;
    i <- 0;
    while (i < 2^t) {
      address <- set_type address 0;
      address <- set_ots_addr address (s + 1);

      (* Generate the public key from the secret seed *)
      (pk, address) <@ WOTS.pkGen(sk_seed, pub_seed, address);

      address <- set_type address 1;
      address <- set_tree_addr address (s + i);

      (* compress the WOTS public key into a single N-byte value *)
      (node, address) <@ LTree.ltree(pk, address, pub_seed); 

      address <- set_type address 2;
      address <- set_tree_height address 0;
      address <- set_tree_index address (i + 1);

      (* while ( Top node on Stack has same height t' as node ) *)
      if (1 < offset) {
        j <- 0;
        while (j < t) { (* The stack has at most t - 1 elements *)
          tree_index <- get_tree_index address;
          address <- set_tree_index address (ceil((tree_index - 1)%r / 2%r));
          
          top_node <- nth witness stack (offset - 1); (* Same as Stack.pop() *)
          (node, address) <@ Hash.rand_hash (top_node, node, pub_seed, address);

          j <- j + 1;
        }
      }

      stack <- put stack offset node; (* Same as Stack.push() *)
      offset <- offset + 1;
      i <- i + 1;
    }

    node <- nth witness stack (offset - 1); 
    return (node, address);
  }
}.


module TreeSig = {
  (* Compute the authentication path for the i-th WOTS+ key pair *)
  proc buildAuthPath(pub_seed sk_seed : seed, idx : W32.t, address : adrs) : auth_path * adrs = {
    var authentication_path : nbytes list;
    var j : int ;
    var k : int;
    var t : nbytes <- witness;

    authentication_path <- nseq len witness;

    j <- 0;
    while (j < h) {
      k <- floor((W32.to_uint idx)%r / (2^j)%r);
      (t, address) <@ TreeHash.treehash(pub_seed, sk_seed , k * (2^j), j, address);
      authentication_path <- put authentication_path j t;
      j <- j + 1;
    }

    return (AuthPath.insubd authentication_path, address);
  }

  (* Generate a WOTS+ signature on a message with corresponding authentication path *)
  proc treesig(M : nbytes, pub_seed sk_seed : seed, idx : W32.t, address : adrs) : wots_signature * auth_path * adrs  = {
    var auth : auth_path;
    var sig_ots : wots_signature;
    var ots_sk : wots_sk;
    var seed : nbytes;
    
    (auth, address) <@ buildAuthPath (pub_seed, sk_seed, idx, address);
    address <- set_type address 0;
    address <- set_ots_addr address (W32.to_uint idx);

    (sig_ots, address) <@ WOTS.sign_seed(val M, sk_seed, pub_seed, address);
    
    return (sig_ots, auth, address);
  }
}.

(**********************************************************************************************)

op append_sig (sig : sig_t) (r_sig : reduced_signature) : sig_t =    
    let new_sigs: reduced_signature list = sig.`r_sigs ++ [r_sig] in
    {| sig with  r_sigs=new_sigs|}.

(**********************************************************************************************)

module RootFromSig = {
  proc rootFromSig(idx_sig : W32.t, sig_ots : wots_signature, auth : auth_path, M : nbytes, 
  _seed : seed, address : adrs) : nbytes = {
    var pk_ots : wots_pk;
    var k : int;
    var nodes0, nodes1 : nbytes;
    var index : int;
    var auth_k : nbytes;
    
    address <- set_type address 0;
    address <- set_ots_addr address (W32.to_uint idx_sig);

    (pk_ots, address) <@ WOTS.pkFromSig(M, sig_ots, _seed, address);

    address <- set_type address 1;
    address <- set_ltree_addr address (W32.to_uint idx_sig);

    (nodes0, address) <@ LTree.ltree(pk_ots, address, _seed);

    address <- set_type address 2;
    address <- set_tree_index address (W32.to_uint idx_sig);

    k <- 0;
    while (k < h) {
      address <- set_tree_height address k;

      if (floor ((W32.to_uint idx_sig)%r / (2^k)%r) %% 2 = 0) {
        index <- get_tree_index address;
        address <- set_tree_index address (index %/ 2);

        auth_k <- nth witness (val auth) k;
        (nodes1, address) <@ Hash.rand_hash (nodes0, auth_k, _seed, address);
      } else {
        index <- get_tree_index address;
        address <- set_tree_index address ((index - 1) %/ 2);

        auth_k <- nth witness (val auth) k;
        (nodes1, address) <@ Hash.rand_hash (auth_k, nodes0, _seed, address);
      }

      nodes0 <- nodes1;
      k <- k+1;
    }

    return nodes0;
  }
}.
