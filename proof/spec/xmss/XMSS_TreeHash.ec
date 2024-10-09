pragma Goals : printall.


require import AllCore List RealExp IntDiv Distr DList.
require (*--*) Subtype. 

from Jasmin require import JModel.
 
require import XMSS_Types Address LTree Hash.


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
  proc treehash(pub_seed sk_seed : seed, s t : int, address : adrs) : nbytes = {
    var node : nbytes;
    var stack : nbytes list;
    var pk : wots_pk;
    var offset : int;
    var i, j : int;
    var tree_index : int;
    var top_node : nbytes;

    stack <-  nseq (h + 1) (NBytes.insubd (nseq n W8.zero));
    offset <- 0;
    i <- 0;
    while (i < 2^t) {
      address <- set_type address 0;
      address <- set_ots_addr address (s + i);

      (* Generate the public key from the secret seed *)
      pk <@ WOTS.pkGen(sk_seed, pub_seed, address);

      address <- set_type address 1;
      address <- set_tree_addr address (s + i);

      (* compress the WOTS public key into a single N-byte value *)
      node <@ LTree.ltree(pk, address, pub_seed); 

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
          node <@ Hash.rand_hash (top_node, node, pub_seed, address);

          j <- j + 1;
        }
      }

      stack <- put stack offset node; (* Same as Stack.push() *)
      offset <- offset + 1;
      i <- i + 1;
    }

    node <- nth witness stack (offset - 1); 
    return node;
  }
}.


module TreeSig = {
  (* Compute the authentication path for the i-th WOTS+ key pair *)
  proc buildAuthPath(pub_seed sk_seed : seed, idx : W32.t, address : adrs) : auth_path = {
    var authentication_path : nbytes list;
    var j : int <- 0;
    var k : int;
    var t : nbytes <- witness;
 
    authentication_path <- nseq h witness;

    while (j < h) {
      (* k <- floor((W32.to_uint idx)%r / (2^j)%r); XOR ONE *)
      k <- to_uint ((idx `>>` (of_int j)%W8) `^` W32.one); (* Does this make sense ???? I think so *)
      t <@ TreeHash.treehash(pub_seed,sk_seed, k * (2^j), j, address);
      authentication_path <- put authentication_path j t;
      j <- j + 1;
    }

    return AuthPath.insubd authentication_path;
  }

  (*
   Algorithm 11: treeSig - Generate a WOTS+ signature on a message with
   corresponding authentication path

     Input: n-byte message M', XMSS private key SK,
            signature index idx_sig, ADRS
     Output: Concatenation of WOTS+ signature sig_ots and
             authentication path auth
  *)
  proc treesig(M : nbytes, pub_seed sk_seed : seed, idx : W32.t, address : adrs) : wots_signature * auth_path  = {
    var auth : auth_path;
    var sig_ots : wots_signature;
    var ots_sk : wots_sk;
    var seed : nbytes;
    
    auth <@ buildAuthPath (pub_seed,sk_seed, idx, address);
    address <- set_type address 0;
    address <- set_ots_addr address (W32.to_uint idx);

    sig_ots <@ WOTS.sign_seed(val M, sk_seed, pub_seed, address);
    
    return (sig_ots, auth);
  }
}.

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

    pk_ots <@ WOTS.pkFromSig(M, sig_ots, _seed, address);

    address <- set_type address 1;
    address <- set_ltree_addr address (W32.to_uint idx_sig);

    nodes0 <@ LTree.ltree(pk_ots, address, _seed);

    address <- set_type address 2;
    address <- set_tree_index address (W32.to_uint idx_sig);

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
      k <- k+1;
    }

    return nodes0;
  }
}.
