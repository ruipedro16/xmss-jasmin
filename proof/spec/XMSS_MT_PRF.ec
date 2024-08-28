pragma Goals : printall.

require import AllCore List RealExp IntDiv.
require (*--*) Subtype. 

from Jasmin require import JModel.
 
require import Types Params Notation Parameters Address Hash Primitives Wots Util.
 
import NBytes OTSKeys Three_NBytes AuthPath.
import Array8.

(**********************************************************************************************)

op H : nbytes -> nbytes -> nbytes.
op H_msg : three_n_bytes -> W8.t list -> nbytes.
op impl_oid : W32.t.

(**********************************************************************************************)

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

    address <- set_tree_height address 0;

    while (1 < _len) { (* Same as _len > 1 *)
      i <- 0;
      while (i < floor (_len%r / 2%r)) {
        address <- set_tree_index address i;
        pk_i <- nth witness pk (2*i);
        tmp <- nth witness pk (2*i + 1);
        (pk_i, address) <@ Hash.rand_hash (pk_i, tmp, _seed, address);
        pk <- put pk i pk_i;
      }

      if (_len %% 2 = 1) {
        pk_i <- nth witness pk (_len - 1);
        pk <- put pk (floor (len%r / 2%r)) pk_i;
      }

      _len <- ceil (len%r / 2%r);
      i <- i + 1;
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
while (0 <= _len <= len) (floor (len%r / 2%r) - i).
auto => />; call rand_hash_ll. wp. skip => /> *. 
rewrite !negb_and.
left; left. 
admit.

auto => /> *. do split. 
smt(). 
admit.
smt().
move => *. admit.
qed.

lemma ltree_size : hoare [LTree.ltree : true ==> size res.`1 = n].
proof.
proc.
seq 3 : (true); first by auto.
seq 1 : (forall (x : W8.t list), x \in pk => size pk = n); last first.
  + auto => /> &hr *. admit.
admit.
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
  var node : nbytes;
  var stack : nbytes list;
  var top_node : nbytes;
  var pub_seed : seed <- sk.`pub_seed_sk;
  var sk_seed : seed <- sk.`sk_seed;
  var pk : wots_pk;
  var i : int <- 0;
  var tree_index, tree_height: int;
  var heights : int list <- nseq (h + 1) 0; (* TODO: Check if this is the correct size *)
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


op append_sig (sig : sig_t) (r_sig : reduced_signature) : sig_t =    
    let new_sigs: reduced_signature list = sig.`r_sigs ++ [r_sig] in
    {| sig with  r_sigs=new_sigs|}.

module XMSS = {
  proc rootFromSig(idx_sig : W32.t, sig_ots : wots_signature, auth : auth_path, M : nbytes, 
                   _seed : seed, address : adrs) : nbytes = {
    var pk_ots : wots_pk;
    var k : int <- 0;
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

module XMSS_MT_PRF = {
   (* Different from the spec because we use a secret seed instead of the full wots keys *)
   (* Algorithm 10 instead of 15 *)
   (*
            +---------------------------------+
            |          algorithm OID          |     W32 (4 bytes)
            +---------------------------------+
            |                                 |
            |            root node            |     n bytes
            |                                 |
            +---------------------------------+
            |                                 |
            |              SEED               |     n bytes
            |                                 |
            +---------------------------------+

                            XMSS^MT Public Key
   *)
   proc kg() : xmss_mt_keypair = {
      var pk : xmss_mt_pk <- witness;
      var sk : xmss_mt_sk <- witness;

      var sk_seed, sk_prf, pub_seed, root : nbytes;

      var address : adrs <- zero_address;
      
      sk_seed <$ DList.dlist W8.dword n;
      sk_prf <$ DList.dlist W8.dword n;
      pub_seed <$ DList.dlist W8.dword n;

      (root, address) <@ TreeHash.treehash(sk, 0, h, address);

      sk <- {| idx=W32.zero;
               sk_seed=sk_seed;
               sk_prf=sk_prf;
               pub_seed_sk=pub_seed;
               sk_root=root;
             |};

      pk <- {| pk_oid=impl_oid; pk_root=root; pk_pub_seed=pub_seed |};

      return (sk, pk);
   }

  
   (* Algorithm 13 *)
   proc rootFromSig(idx_sig : W32.t, sig_ots : wots_signature, auth : auth_path, M : nbytes, 
                   _seed : seed, address : adrs) : nbytes = {
    var pk_ots : wots_pk;
    var k : int <- 0;
    var nodes0, nodes1 : nbytes <- nseq n W8.zero;
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
 
    while (k < h) {
      address <- set_tree_height address k;

      if (floor ((W32.to_uint idx_sig)%r / (2^k)%r) %% 2 = 0) {
        index <- get_tree_index address;
        address <- set_tree_index address (index %/ 2);

        auth_k <- nth witness auth k;
        (nodes1, address) <@ Hash.rand_hash(nodes0, auth_k, _seed, address);
      } else {
        index <- get_tree_index address;
        address <- set_tree_index address ((index - 1) %/ 2);

        auth_k <- nth witness auth k;
        (nodes1, address) <@ Hash.rand_hash(auth_k, nodes0, _seed, address);
      }

      nodes0 <- nodes1;
      k <- k+1;
    }

    return nodes0;
  }

   (*
           +---------------------------------+
           |                                 |
           |          index idx_sig          |   ceil(h / 8) bytes
           |                                 |
           +---------------------------------+
           |                                 |
           |          randomness r           |   n bytes
           |                                 |
           +---------------------------------+
           |                                 |
           |  (reduced) XMSS signature Sig   |   (h / d + len) * n bytes
           |        (bottom layer 0)         |
           |                                 |
           +---------------------------------+
           |                                 |
           |  (reduced) XMSS signature Sig   |   (h / d + len) * n bytes
           |            (layer 1)            |
           |                                 |
           +---------------------------------+
           |                                 |
           ~              ....               ~
           |                                 |
           +---------------------------------+
           |                                 |
           |  (reduced) XMSS signature Sig   |   (h / d + len) * n bytes
           |          (layer d - 1)          |
           |                                 |
           +---------------------------------+

                             XMSS^MT Signature
   *)
   proc sign(sk : xmss_mt_sk, m : msg_t) : sig_t * xmss_mt_sk = {
      var sig : sig_t;
      var idx : W32.t <-sk.`idx;
      var idx_new : W32.t;
      var idx_bytes : W8.t list;
      var idx_nbytes : nbytes <- nseq n W8.zero;
      var idx_tree : W32.t;
      var idx_leaf : W32.t;
      var _R : nbytes <- nseq n W8.zero;
      var _M' : nbytes <- nseq n W8.zero;
      var address : adrs <- zero_address;
      var root : nbytes <- sk.`sk_root;
      var t : three_n_bytes <- nseq (3*n) W8.zero;
      var sk_prf : nbytes <- sk.`sk_prf;
      var j : int;
      var pub_seed : nbytes <- sk.`pub_seed_sk;
      var sig_tmp : wots_signature;
      var auth : auth_path;
    

      (* Update the key index *)
      idx_new <- idx + W32.one;
      sk <- {| sk with idx=idx_new |};

      idx_bytes <- toByte idx 32;
      _R <@ Hash.prf(sk_prf, idx_bytes);

      idx_nbytes <- toByte idx n;
      t <- _R ++ root ++ idx_nbytes; (* t = r || getRoot(SK_MT) || (toByte(idx_sig, n)) *)
      _M' <- H_msg t m;

      idx_tree <- msb_w32_int idx (h - (h %/ d));
      idx_leaf <- msb_w32_int idx (h %/ d);

      address <- set_layer_addr address 0;
      address <- set_tree_addr address (W32.to_uint idx_tree);

      (sig_tmp, auth, address) <@ TreeSig.treesig(_M', sk, idx_leaf, address);
     
      sig <- {| sig with r_sigs = [(sig_tmp, auth)] |}; (* Sig_MT = Sig_MT || r || Sig_tmp; *)

      j <- 1;
      while (j < d) {
      (root, address) <@ TreeHash.treehash(sk, 0, h %/ d, address);
      idx_leaf <- lsb_w32_int idx_tree (h %/ d);
      idx_tree <- msb_w32_int idx_tree (h - (j * (h %/ d)));
      
      address <- set_layer_addr address j;
      address <- set_tree_addr address (W32.to_uint idx_tree);

      (sig_tmp, auth, address) <@ TreeSig.treesig(root, sk, idx_leaf, address);
      
      sig <- append_sig sig (sig_tmp, auth);
      
       
      j <- j+1;
    }
      

      return (sig, sk);
   }

  (* Algorithm 14 *)
   proc verify(pk : xmss_mt_pk, m : msg_t, s : sig_t) : bool = {
       var is_valid : bool;
       var idx_sig : W32.t <- s.`sig_idx;
       var seed : nbytes <- pk.`pk_pub_seed;
       var idx_bytes : nbytes <- toByte idx_sig n;
       var node, root, _R, _M': nbytes;
       var t : three_n_bytes;
       var address : adrs <- zero_address;
       var j : int;
     
       var idx_leaf : W32.t <- lsb_w32_int idx_sig (h %/ d);
       var idx_tree : W32.t <- msb_w32_int idx_sig (h - (h %/ d));
     
       var _sig : reduced_signature <- nth witness s.`r_sigs 0;
     
       (* M' = H_msg(getR(Sig_MT) || getRoot(PK_MT) || (toByte(idx_sig, n)), M); *)
       root <- pk.`pk_root;
       t <- _R ++ root ++ idx_bytes;
       _M' <- H_msg t m; 

       address <- set_layer_addr address 0;
       address <- set_tree_addr address (W32.to_uint idx_tree);

       node <@ XMSS.rootFromSig(idx_leaf, _sig.`1, _sig.`2, _M', seed, address);
     
       j <- 1;
       while (j < d) {
         idx_leaf <- lsb_w32_int idx_tree (h %/ d);
         idx_tree <- msb_w32_int idx_tree (h - (h %/ d));

         _sig <- nth witness s.`r_sigs j;

         address <- set_layer_addr address j;
         address <- set_tree_addr address (W32.to_uint idx_tree);
       
         node <@ XMSS.rootFromSig(idx_leaf, _sig.`1, _sig.`2, _M', node, address);

         j <- j + 1;
       }

       
           is_valid <- (node = root);
           return is_valid;
   }
}.

lemma xmss_mt_kg_ll : islossless XMSS_MT_PRF.kg.
proof.
proc.
auto => /> ; call treehash_ll.
auto => /> *; smt(@Distr @DList @W8).
qed.

lemma root_from_sig_ll : islossless XMSS_MT_PRF.rootFromSig.
proof.
proc.
while (0 <= k <= h) (h - k) ; auto => />; 1,2:admit. (* by progress ; smt(). *)
call ltree_ll ; auto => />. 
call wots_pkFromSig_ll ; auto => />.
smt(h_g0).
qed.

lemma xmss_mt_sign_ll : islossless XMSS_MT_PRF.sign.
proof.
proc.
while (0 <= j <= d) (d - j) ; auto => />.
  - call treesig_ll ; auto => />. call treehash_ll. skip => /> /#.
  - progress ; smt().
  - call treesig_ll; wp.  call prf_ll; wp.  skip => />; smt(ge0_d). 
qed. 

