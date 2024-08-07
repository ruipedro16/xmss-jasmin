pragma Goals : printall.

require import AllCore List RealExp IntDiv.
require (*--*) Subtype. 

from Jasmin require import JModel.

require import Params Notation Parameters Address Primitives Wots.

import NBytes.
import Array8.

clone import Subtype as Three_NBytes with 
   type T = W8.t list,
   op P = fun l => size l = 3 * n
   rename "T" as "three_n_bytes"
   proof inhabited by (exists (nseq (3*n) W8.zero);smt(size_nseq ge0_n))
   proof *.

clone import Subtype as OTSKeys with 
   type T = wots_sk list,
   op P = fun l => size l = 2^h
   rename "T" as "wots_ots_keys".

clone import Subtype as AuthPath with
  type T = nbytes list,
  op P = fun l => size l = len
  rename "T" as "auth_path"
  proof inhabited by (exists (nseq len (nseq n W8.zero));smt(size_nseq ge0_len))
  proof *.

op d : { int | 1 <= d } as ge1_d. (* d layers of trees, each having height h/d  *)
op h : { int | 0 <= h /\ h %% d = 0} as h_vals. (* hyper-tree of total height h, where h is a multiple of d *)

(**********************************************************************************************)

(* gets the n most significant bits *)
op msb (x : W8.t list) (n : int) : W8.t list = take n x. 

(* gets the n most significant bits of x *)
(* n is at most 32 *)
op msb_w32 (x : W32.t) (n : int) : bool list = take n (w2bits x).

(* Returns the n most significant bits of x as a W32.t *)
op msb_w32_int (x : W32.t) (n : int) : W32.t = 
  let bits : bool list = take n (w2bits x) in
  (W32.bits2w bits).

op lsb_w32_int (x : W32.t) (n : int) : W32.t =
   let bits : bool list =  w2bits x in
   let lsbits : bool list =  drop ((size bits) - n) bits in
   W32.bits2w lsbits.

(**********************************************************************************************)

op H : nbytes -> bitmask -> nbytes.
op H_msg : three_n_bytes -> W8.t list -> nbytes.
op _prf_ : nbytes -> W8.t list -> nbytes.
op impl_oid : W32.t.

(**********************************************************************************************)

type xmss_mt_sk = { idx : W32.t ;
                    sk_seed : nbytes ; (* secret *)
                    sk_prf : nbytes ;
                    pub_seed_sk : nbytes ; (* public *)
                    sk_root : nbytes }.

type xmss_mt_pk = { pk_oid : W32.t ;
                    pk_root : nbytes ;
                    pk_pub_seed : nbytes }.

type msg_t = W8.t list.

type sig_t = { sig_idx : W32.t;
               r : nbytes;
               wots_sig : wots_signature;
               authentication_path : auth_path }.

type xmss_mt_keypair = xmss_mt_sk * xmss_mt_pk.

(**********************************************************************************************)

(* 4.1.4 Randomized tree hashing *)
module RandHash = {
proc rand_hash (_left _right : nbytes, _seed : seed, address : adrs) : nbytes * adrs = { 
  var key : nbytes;
  var bitmask_0 : nbytes;
  var bitmask_1 : nbytes;
  var hash_in : nbytes;

  address <- set_key_and_mask address 0;
  key <- PRF _seed address;
  address <- set_key_and_mask address 1;
  bitmask_0 <- PRF _seed address;
  address <- set_key_and_mask address 2;
  bitmask_1 <- PRF _seed address;
  hash_in <- (nbytexor _left bitmask_0) ++ (nbytexor _right bitmask_1);
  
  return (H key hash_in, address);
  }
}.
(**********************************************************************************************)

(* 4.1.5 L-Trees *)
module LTree = {
  proc ltree (pk : wots_pk, address : adrs, _seed : seed) : nbytes * adrs = {
    var pk_i : nbytes;
    var tmp : nbytes;
    var i : int <- witness;
    var _len : int <- len;

    address <- set_tree_height address 0;

    while (1 < _len) { (* Same as _len > 1 *)
      i <- 0;
      while (i < floor (len%r / 2%r)) {
        address <- set_tree_index address i;
        pk_i <- nth witness pk (2*i);
        tmp <- nth witness pk (2*i + 1);
        (pk_i, address) <@ RandHash.rand_hash (pk_i, tmp, _seed, address);
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


lemma neg_lt (x y : int) : ! (x < y) <=> y <= x by smt().


lemma ltree_ll : islossless LTree.ltree.
proof.
proc.
sp ; wp.
while (1 <= _len <= len) (_len - 1) ; auto => />.
- while (0 <= i <= floor (len%r / 2%r)) (floor (len%r / 2%r) - i) ; auto => />.
  + progress.  admit.
  + progress; 1,2,3,4,5: by admit.
- admit. (* split ;  [ smt(ge0_len) | move => * ; rewrite neg_lt /# ]. *)
qed.

(**********************************************************************************************)

(* Stack operations *)
abbrev push (x : 'a list) (a : 'a) : 'a list = rcons x a. 

op remove_last (x : 'a list) : 'a list = 
with x = [] => []
with x = h::t => if t = [] then [] else remove_last t.

abbrev pop (x : 'a list) : 'a list * 'a = 
    let last_elem : 'a = last witness x in
    let new_list = remove_last x in
    (new_list, last_elem).

(* It is REQUIRED that s % 2^t = 0, i.e., that the leaf at index s is a leftmost leaf of a sub-tree of height t. *)
pred leftmost_leaf (s t : int)  = s %% 2^t = 0.

pred treehash_p (s t : int) = s %% (1 `<<` t) <> 0.


(* NOTE: In the implementation, treehash (in xmss_core.c) computes both the authentication 
         path and the resulting root node *)
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
  var heights : int list;
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

        (node, address) <@ RandHash.rand_hash (top_node, node, pub_seed, address);
        
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
while (true) (2^t - i) ; auto => /> ; last by progress ; rewrite neg_lt /#.
sp ; wp. 
admit.
qed.

module TreeSig = {
  proc buildAuthPath(sk : xmss_mt_sk, idx : W32.t, address : adrs) : auth_path * adrs = {
    var authentication_path : auth_path;
    
    var j : int <- 0;
    var k : int;
    var t : nbytes <- witness;

    while (j < h) {
      k <- floor((W32.to_uint idx)%r / (2^j)%r);
      (t, address) <@ TreeHash.treehash(sk, k * (2^j), j, address);
      authentication_path <- put authentication_path j t;
      j <- j+1;
    }

    return (authentication_path, address);
  }

  proc treesig(M : nbytes, sk : xmss_mt_sk, idx : W32.t, address : adrs) : wots_signature * auth_path * adrs  = {
    var auth : auth_path;
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
while (0 <= j <= h) (h - j) ; auto => />.
  - call treehash_ll ; auto => /> /#. 
  - split ; smt(h_vals). 
qed.

lemma treesig_ll : islossless TreeSig.treesig.
proof.
proc.
call wots_sign_seed_ll.
auto => /> ; call buildAuthPath_ll.
by skip.
qed.

module XMSS_MT_PRF = {
   proc kg() : xmss_mt_keypair = {
      var pk : xmss_mt_pk <- witness;
      var sk : xmss_mt_sk <- witness;

      var idx_MT : W32.t <- W32.zero;
      var sk_seed, sk_prf, pub_seed, root : nbytes;

      var address : adrs <- zero_address;
      
      sk_seed <$ DList.dlist W8.dword n;
      sk_prf <$ DList.dlist W8.dword n;
      pub_seed <$ DList.dlist W8.dword n;

      (root, address) <@ TreeHash.treehash(sk, 0, h, address);

      sk <- {| idx=idx_MT;
               sk_seed=sk_seed;
               sk_prf=sk_prf;
               pub_seed_sk=pub_seed;
               sk_root=root;
             |};

      pk <- {| pk_oid=impl_oid; pk_root=root; pk_pub_seed=pub_seed |};

      return (sk, pk);
   }

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
        (nodes1, address) <@ RandHash.rand_hash(nodes0, auth_k, _seed, address);
      } else {
        index <- get_tree_index address;
        address <- set_tree_index address ((index - 1) %/ 2);

        auth_k <- nth witness auth k;
        (nodes1, address) <@ RandHash.rand_hash(auth_k, nodes0, _seed, address);
      }

      nodes0 <- nodes1;
      k <- k+1;
    }

    return nodes0;
  }



   proc sign(sk : xmss_mt_sk, m : msg_t) : sig_t * xmss_mt_sk = {
      var sig : sig_t;
      var idx : W32.t <-sk.`idx;
      var idx_new : W32.t;
      var idx_bytes : W8.t list;
      var idx_nbytes : nbytes;
      var idx_tree : W32.t;
      var idx_leaf : W32.t;
      var _R : nbytes;
      var _M' : nbytes;
      var address : adrs <- zero_address;
      var root : nbytes <- sk.`sk_root;
      var t : three_n_bytes;
      var sk_prf : nbytes <- sk.`sk_prf;
      var j : int;
      var pub_seed : nbytes <- sk.`pub_seed_sk;
      var sig_tmp : wots_signature;
      var auth : auth_path;
    

      (* Update the key index *)
      idx_new <- idx + W32.one;
      sk <- {| sk with idx=idx_new |};

      idx_bytes <- toByte idx 32;
      _R <- _prf_ sk_prf idx_bytes;

      idx_nbytes <- toByte idx n;
      t <- _R ++ root ++ idx_nbytes;
      _M' <- H_msg t m;

      idx_tree <- msb_w32_int idx (h - (h %/ d));
      idx_leaf <- msb_w32_int idx (h %/ d);

      address <- set_layer_addr address 0;
      address <- set_tree_addr address (W32.to_uint idx_tree);

      (sig_tmp, auth, address) <@ TreeSig.treesig(_M', sk, idx_leaf, address);
     
      (* sig <- {| sig with reduced_sig_mt=[(sig_tmp, auth)] |}; *)

      j <- 1;
      while (j < d) {
      (root, address) <@ TreeHash.treehash(sk, 0, h %/ d, address);
      idx_leaf <- lsb_w32_int idx_tree (h %/ d);
      idx_tree <- msb_w32_int idx_tree (h - (j * (h %/ d)));
      
      address <- set_layer_addr address j;
      address <- set_tree_addr address (W32.to_uint idx_tree);

      (sig_tmp, auth, address) <@ TreeSig.treesig(root, sk, idx_leaf, address);
      
      (* sig <- append_sig sig (sig_tmp, auth); *)
      
      
      j <- j+1;
    }
      

      return (sig, sk);
   }

  (*
   proc verify(pk : xmss_mt_pk, m : msg_t, s : sig_t) : bool = {
     var is_valid : bool;
     (* var idx : W32.t <- s.`sig_idx_mt; *)
     (* var idx_bytes : nbytes <- toByte idx n; *)
     var seed : nbytes <- pk.`pk_pub_seed;
     var address : adrs <- zero_address;
     (* var idx_leaf : W32.t <- lsb_w32_int idx (h %/ d); *)
     (* var idx_tree : W32.t <- msb_w32_int idx (h - (h %/ d)); *)
     (* var _sig : reduced_sig; *)
     var node, root, _R, _M': nbytes;
     var t : three_n_bytes;
     var j : int;

      (* _sig <- nth witness s.`reduced_sig_mt 0; *)

      (* _R <- s.`r_mt; *)
     root <- pk.`pk_root;
     t <- _R ++ root ++ idx_bytes;
      _M' <- H_msg t m; 
     
     node <@ XMSS.rootFromSig(idx_leaf, _sig.`1, _sig.`2, _M', seed, address);

     j <- 1;
     while (j < d) {
       (* idx_leaf <- lsb_w32_int idx_tree (h %/ d); *)
       (* idx_tree <- msb_w32_int idx_tree (h - (h %/ d)); *)

       (* _sig <- nth witness s.`reduced_sig_mt j; *)
      
       address <- set_layer_addr address j;
       address <- set_tree_addr address (W32.to_uint idx_tree);

       node <@ XMSS.rootFromSig(idx_leaf, _sig.`1, _sig.`2, _M', seed, address);

       j <- j + 1;
     }

    is_valid <- (node = root);



     return is_valid;
   }
   *)
}.

lemma xmss_mt_kg_ll : islossless XMSS_MT_PRF.kg.
proof.
proc.
auto => /> ; call treehash_ll.
auto => /> *. smt(@Distr @DList @W8).
qed.

lemma root_from_sig_ll : islossless XMSS_MT_PRF.rootFromSig.
proof.
proc.
while (0 <= k <= h) (h - k) ; auto => />; 1,2:admit. (* by progress ; smt(). *)
call ltree_ll ; auto => />. 
call wots_pkFromSig_ll ; auto => />.
smt(h_vals).
qed.

lemma xmss_mt_sign_ll : islossless XMSS_MT_PRF.sign.
proof.
proc.
while (0 <= j <= d) (d - j) ; auto => />.
  - call treesig_ll ; auto => />. call treehash_ll. skip => /> /#.
  - progress ; smt().
  - call treesig_ll ; auto => /> ; smt(ge1_d).
qed.


