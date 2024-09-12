pragma Goals : printall.


require import AllCore List RealExp IntDiv Distr DList.
require (*--*) Subtype. 

from Jasmin require import JModel.
 
require import Types Params Notation Parameters Address Hash Primitives Wots Util.
 
import OTSKeys Three_NBytes AuthPath.
import Array8.

op H : nbytes -> nbytes -> nbytes.
op H_msg : three_n_bytes -> W8.t list -> nbytes.
op impl_oid : W32.t.

(* 4.1.5 L-Trees *)
(* takes as input a WOTS+ public key pk and compresses it to a single 
   n-byte value pk[0].
*)
module LTree = {
  proc ltree (pk : wots_pk, address : adrs, _seed : seed) : nbytes * adrs = {
    var pk_i : nbytes;
    var tmp : nbytes;
    var i : int <- witness;
    var _len : int <- len;
    var tree_height : int;

    address <- set_tree_height address 0;

    while (1 < _len) { (* Same as _len > 1 *)
      i <- 0;
      while (i < floor (_len%r / 2%r)) {
        address <- set_tree_index address i;
        pk_i <- nth witness pk (2*i);
        tmp <- nth witness pk (2*i + 1);
        (pk_i, address) <@ Hash.rand_hash (pk_i, tmp, _seed, address);
        pk <- put pk i pk_i;
        i <- i + 1;
      }

      if (_len %% 2 = 1) {
        pk_i <- nth witness pk (_len - 1);
        pk <- put pk (floor (len%r / 2%r)) pk_i;
      }

      _len <- ceil (_len%r / 2%r);

      tree_height <- get_tree_height address;
      address <- set_tree_height address (tree_height + 1);
    }

    pk_i <- nth witness pk 0;

    return (pk_i, address);
  }
}. 


lemma ltree_ll : islossless LTree.ltree.
proof.
proc.
islossless.
while (true) (_len - 1); last by skip => /> /#.
auto => />.
while (_len <= len) (floor (_len%r / 2%r) - i).
auto => />; call rand_hash_ll. wp. skip => /> /#. 
auto => /> &hr ?; do split.  admit. 
move => *. do split; smt(@Real). 
qed.

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
  proc treehash(sk : xmss_mt_sk, s t : int, address : adrs) : nbytes * adrs = {
  var node : nbytes <- nseq n W8.zero;
  var stack : nbytes list;
  var top_node : nbytes;
  var pub_seed : seed <- sk.`pub_seed_sk;
  var sk_seed : seed <- sk.`sk_seed;
  var pk : wots_pk;
  var i : int <- 0;
  var tree_index, tree_height: int;
  var heights : int list <- nseq (h + 1) 0;
  var tmp : int;
  var offset : int <- 0;
    
    while (i < 2^t) {
      (* ----------- not in the RFC ----------- *)
      offset <- offset + 1;
      heights <- put heights (offset - 1) 0; 
      (* -------------------------------------- *)

      address <- set_type address 0;
      address <- set_ots_addr address (s + 1);

      (* Generate the public key from the secret seed *)
      (pk, address) <@ WOTS.pkGen(sk_seed, pub_seed, address);

      address <- set_type address 1;
      address <- set_tree_addr address (s + 1);

      (node, address) <@ LTree.ltree(pk, address, pub_seed); 

      address <- set_type address 2;
      address <- set_tree_height address 0;
      address <- set_tree_index address (i + 1);
      
      top_node <- last witness stack;

      (* While the top-most nodes are of equal height *)
      (* offset >= 2 <=> 2 <= offset *)
      
      while (2 <= offset /\ ((nth witness heights (offset - 1)) = (nth witness heights (offset - 2)))) {
        tree_index <- get_tree_index address;
        address <- set_tree_index address (ceil((tree_index - 1)%r / 2%r));
        (stack, top_node) <- pop stack;

        (node, address) <@ Hash.rand_hash (top_node, node, pub_seed, address);
        
        (* ----------- not in the RFC ----------- *)
        offset <- offset - 1;
        tmp <- nth witness heights (offset - 1);
        heights <- put heights (offset - 1) (t + 1);
        (* -------------------------------------- *)

        tree_height <- get_tree_height address;
        address <- set_tree_height address (tree_height + 1); (* Move to the next tree *)
      }

      stack <- push stack node;
      i <- i + 1;
    }
    
  return (node, address);
  }
}.

lemma treehash_ll : islossless TreeHash.treehash.
proof.
proc.
sp ; wp.
while (true) (2^t - i); last by skip => /> /#.
auto => />. sp.
while (true) (offset - 1).
  + auto => />; call rand_hash_ll; wp; skip => /> /#.
  + wp; call ltree_ll; wp; call wots_pkGen_ll; wp. skip => /> *.
    split; [ move => *; rewrite negb_and; left |]; smt().
qed.

module TreeSig = {
  (* Compute the authentication path for the i-th WOTS+ key pair *)
  proc buildAuthPath(sk : xmss_mt_sk, idx : W32.t, address : adrs) : auth_path * adrs = {
    var authentication_path : auth_path <- nseq len (nseq n W8.zero);
    var j : int <- 0;
    var k : int;
    var t : nbytes <- witness;

    while (j < h) {
      k <- floor((W32.to_uint idx)%r / (2^j)%r);
      (t, address) <@ TreeHash.treehash(sk, k * (2^j), j, address);
      authentication_path <- put authentication_path j t;
      j <- j + 1;
    }

    return (authentication_path, address);
  }

  (* Generate a WOTS+ signature on a message with corresponding authentication path *)
  proc treesig(M : nbytes, sk : xmss_mt_sk, idx : W32.t, address : adrs) : wots_signature * auth_path * adrs  = {
    var auth : auth_path <- nseq len (nseq n W8.zero);
    var sig_ots : wots_signature;
    var ots_sk : wots_sk;
    var seed : nbytes;
    
    (auth, address) <@ buildAuthPath (sk, idx, address);
    address <- set_type address 0;
    address <- set_ots_addr address (W32.to_uint idx);

    (sig_ots, address) <@ WOTS.sign_seed(M, sk.`sk_seed, sk.`pub_seed_sk, address);
    
    return (sig_ots, auth, address);
  }
}.

lemma buildAuthPath_ll : islossless TreeSig.buildAuthPath.
proof.
proc.
while (0 <= j <= h) (h - j) ; auto => />; [call treehash_ll ; auto => /> /# | smt(h_g0) ]. 
qed.

lemma treesig_ll : islossless TreeSig.treesig
    by proc; call wots_sign_seed_ll; auto => /> ; call buildAuthPath_ll; auto.

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

        auth_k <- nth witness auth k;
        (nodes1, address) <@ Hash.rand_hash (nodes0, auth_k, _seed, address);
      } else {
        index <- get_tree_index address;
        address <- set_tree_index address ((index - 1) %/ 2);

        auth_k <- nth witness auth k;
        (nodes1, address) <@ Hash.rand_hash (auth_k, nodes0, _seed, address);
      }

      nodes0 <- nodes1;
      k <- k+1;
    }

    return nodes0;
  }
}.

lemma root_from_sig_ll : islossless RootFromSig.rootFromSig.
proof.
proc.
while (0 <= k <= h) (h - k) ; auto => />.
  + wp; sp. if. 
      * call rand_hash_ll. islossless. auto => /> &hr *; do split; admit. 
      * call rand_hash_ll. islossless. auto => /> &hr *; do split; admit.
  + auto => />; do split => /#.
  + call ltree_ll ; auto => />. 
    call wots_pkFromSig_ll ; auto => />.
    smt(h_g0).
qed.

