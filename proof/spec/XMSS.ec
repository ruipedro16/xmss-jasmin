require import AllCore List RealExp IntDiv.
require Subtype. 

from Jasmin require import JModel.

require import Params Notation Parameters Address Primitives Wots.

import NBytes.
import Array8.

clone import Subtype as Bitmask with 
   type T = byte list,
   op P = fun l => size l = 2 * n
   rename "T" as "bitmask"
   proof inhabited by (exists (nseq (2*n) W8.zero);smt(size_nseq ge0_n))
   proof *.

clone import Subtype as Three_NBytes with 
   type T = byte list,
   op P = fun l => size l = 3 * n
   rename "T" as "three_n_bytes"
   proof inhabited by (exists (nseq (3*n) W8.zero);smt(size_nseq ge0_n))
   proof *.

op d : { int | 0 < d } as g0_d. (* d layers of trees, each having height h/d  *)
op h : { int | 0 < h /\ h %% d = 0} as h_vals. (* hyper-tree of total height h, where h is a multiple of d *)

(* NOTE: XMSS is the same as XMSS_MT with d = 1 *)

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

(*********************************************************************************************)

(*
Section 4.1.2. of the RFC

Besides the cryptographic hash function F and the pseudorandom
function PRF required by WOTS+, XMSS uses two more functions:

-  A cryptographic hash function H.  H accepts n-byte keys and byte
      strings of length 2n and returns an n-byte string.

-  A cryptographic hash function H_msg.  H_msg accepts 3n-byte keys
      and byte strings of arbitrary length and returns an n-byte string.


See also Section 5.1. 
 *)
op H : nbytes -> bitmask -> nbytes.
op H_msg : three_n_bytes -> byte list -> nbytes.

op _prf_ : nbytes -> byte list -> nbytes.

type oid =  W32.t.
op _oid : oid.

(* Format sk: [OID || (ceil(h/8) bit) idx || SK_SEED || SK_PRF || PUB_SEED || root] *)
(* type sk_t = oid * W32.t * nbytes * nbytes * nbytes * nbytes. *)
type xmss_sk = W32.t * wots_sk list * nbytes * nbytes * nbytes.

(* Format pk: [OID || root || PUB_SEED] *)
type xmss_pk = oid * nbytes * nbytes.

type xmss_keypair = xmss_sk * xmss_pk.

type msg_t = byte list.

type sig_t = W32.t * nbytes * wots_signature * auth_path. (* Section 4.1.8. XMSS Signature *)

op getWOTS_sk (sk : xmss_sk, i : int) : wots_sk = nth witness (sk.`2) i.
op getSK_PRF (sk : xmss_sk) : nbytes = sk.`3.
op getRoot (sk : xmss_sk) : nbytes = sk.`4.
op getRootPK (pk : xmss_pk) : nbytes = pk.`2.
op getIdx (sk : xmss_sk) : W32.t = sk.`1.
op setIdx (sk : xmss_sk, idx : W32.t) : xmss_sk = (idx, sk.`2, sk.`3, sk.`4, sk.`5).
op get_seed (sk : xmss_sk) : nbytes = sk.`5.

(*

            +---------------------------------+
            |          algorithm OID          |
            +---------------------------------+
            |                                 |
            |            root node            |     n bytes
            |                                 |
            +---------------------------------+
            |                                 |
            |              SEED               |     n bytes
            |                                 |
            +---------------------------------+

                              XMSS Public Key

             +---------------------------------+
             |                                 |
             |          index idx_sig          |    4 bytes
             |                                 |
             +---------------------------------+
             |                                 |
             |          randomness r           |    n bytes
             |                                 |
             +---------------------------------+
             |                                 |
             |     WOTS+ signature sig_ots     |    len * n bytes
             |                                 |
             +---------------------------------+
             |                                 |
             |             auth[0]             |    n bytes
             |                                 |
             +---------------------------------+
             |                                 |
             ~              ....               ~
             |                                 |
             +---------------------------------+
             |                                 |
             |           auth[h - 1]           |    n bytes
             |                                 |
             +---------------------------------+

                              XMSS Signature
*)

(**********************************************************************************************)

(* 4.1.4 Randomized tree hashing *)
op rand_hash (_left _right : nbytes, _seed : seed, address : adrs) : nbytes = 
  let address : adrs = set_key_and_mask address 0 in
  let key : nbytes = PRF _seed address in
  let address : adrs = set_key_and_mask address 1 in
  let bitmask_0 : nbytes = PRF _seed address in
  let address : adrs = set_key_and_mask address 2 in
  let bitmask_1 : nbytes = PRF _seed address in
  let hash_in : nbytes = (nbytexor _left bitmask_0) ++ (nbytexor _right bitmask_1) in
  H key hash_in.

(**************************************************************************************************)

(* 4.1.5 L-Trees *)
module LTree = {
  proc ltree (pk : wots_pk, address : adrs, _seed : seed) : nbytes = {
    var _len : int <- len;
    var pk_i : nbytes;
    var tmp : nbytes;
    var i : int <- witness;

    address <- set_tree_height address 0;

    while (1 < _len) { (* Same as _len > 1 *)
      i <- 0;
      while (i < floor (len%r / 2%r)) {
        address <- set_tree_index address i;
        pk_i <- nth witness pk (2*i);
        tmp <- nth witness pk (2*i + 1);
        pk_i <- rand_hash pk_i tmp _seed address;
        pk <- put pk i pk_i;
      }

      if (_len %% 2 = 1) {
        pk_i <- nth witness pk (_len - 1);
        pk <- put pk (floor (len%r / 2%r)) pk_i;
      }

      _len <- ceil (len%r / 2%r);
    }

    pk_i <- nth witness pk 0;

    return pk_i;
  }
}. 

(**************************************************************************************************)

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


(* NOTE: This is slightly different than the RFC *)
(* We need information about the height of the nodes for the loop condition *)
module TreeHash = {
  (* Computes the root *)
  proc treehash(sk : xmss_sk, s t : int, address : adrs) : nbytes = {
    var stack : nbytes list;
    var node : nbytes;
    var ots_sk : wots_sk;
    var top_node : nbytes;
    var _seed : seed;
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

      _seed  <- get_seed sk;
      address <- set_type address 0;
      address <- set_ots_addr address (s + 1);
      
      ots_sk <- getWOTS_sk sk (s+1);
      pk <@ WOTS.genPK (ots_sk, _seed, address);
      address <- set_type address 1;
      address <- set_tree_addr address (s + 1);

      node <@ LTree.ltree(pk, address, _seed); 

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

        node <- rand_hash top_node node _seed address;
        
        (* ----------- not in the RFC ----------- *)
        offset <- offset - 1;
        tmp <- nth witness heights (offset - 1);
        heights <- put heights (offset - 1) (t + 1);
        (* -------------------------------------- *)

        tree_height <- get_tree_height address;
        address <- set_tree_height address (tree_height + 1); (* Move to the next tree *)
      }
      stack <- push stack node;

    }

    (stack, node) <- pop stack;

    return node;
  }
}.

(**************************************************************************************************)

module TreeSig = {
  proc buildAuthPath(sk : xmss_sk, idx : W32.t, address : adrs) : auth_path = {
    var authentication_path : auth_path;
    
    var j : int <- 0;
    var k : int;
    var t : nbytes <- witness;

    while (j < h) {
      k <- floor((W32.to_uint idx)%r / (2^j)%r);
      t <@ TreeHash.treehash(sk, k * (2^j), j, address);
      authentication_path <- put authentication_path j t;
      j <- j+1;
    }

    return authentication_path;
  }

  proc treesig(M : nbytes, sk : xmss_sk, idx : W32.t, address : adrs) : wots_signature * auth_path  = {
    var auth : auth_path;
    var sig_ots : wots_signature;
    var ots_sk : wots_sk;
    var seed : nbytes;
    
    auth <@ buildAuthPath (sk, idx, address);
    address <- set_type address 0;
    address <- set_ots_addr address (W32.to_uint idx);
    ots_sk <- getWOTS_sk sk (W32.to_uint idx);
    seed <- sk.`5;
    sig_ots <@ WOTS.sign(M, ots_sk, seed, address);
    
    return (sig_ots, auth);
  }
}.

(************************************************************************************************)

module XMSS = {
  proc kg() : xmss_keypair = {
    var sk : xmss_sk <- witness;
    var pk : xmss_pk <- witness;

    var idx : W32.t <- W32.zero;
    var i : int <- 0;
    
    var ots_keys : wots_ots_keys <- witness;
    var ots_sk : wots_sk <- witness;

    var address : adrs;

    var sk_prf : nbytes;
    var root : nbytes;
    var seed : nbytes;

    while (i < 2^h) {
      ots_sk <@ WOTS.genSK();
      ots_keys <- put ots_keys i ots_sk;
      i <- i+1;
    }
    
    sk_prf <$ DList.dlist W8.dword n;
    seed <$ DList.dlist W8.dword n;

    address <- zero_address;
    root <@ TreeHash.treehash(sk, 0, h, address);

    sk <- (idx, ots_keys, sk_prf, root, seed);
    pk <- (_oid, root, seed);
    return (sk, pk);
  }

  proc sign(sk : xmss_sk, m : msg_t) : sig_t * xmss_sk = {
    var idx : W32.t;
    var idx_new : W32.t;
    var address : adrs;
    var _R : nbytes;
    var _M' : nbytes;
    var ots_sig : wots_signature;
    var auth : auth_path;
    var sig : sig_t;
    var idx_bytes : byte list;
    var idx_nbytes : nbytes;
    var root : nbytes;
    var t : three_n_bytes;
    
    idx <- getIdx sk;
    idx_new <- idx + W32.one;
    sk <- setIdx sk idx_new;
    address <- zero_address;
    
    idx_bytes <- toByte idx 32;
    _R <- _prf_ (getSK_PRF sk) idx_bytes;

    idx_nbytes <- toByte idx n;
    root <- getRoot sk;
    t <- _R ++ root ++ idx_nbytes;
    _M' <- H_msg t m;

    sig <- (idx, _R, ots_sig, auth);
  
    return (sig, sk);
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

    pk_ots <@ WOTS.pkFromSig(M, sig_ots, _seed, address);

    address <- set_type address 1;
    address <- set_ltree_addr address (W32.to_uint idx_sig);

    nodes0 <@ LTree.ltree(pk_ots, address, _seed);

    address <- set_type address 2;
    address <- set_tree_index address (W32.to_uint idx_sig);

    while (k < h) {
      address <- set_tree_height address k;

      if (floor ((W32.to_uint idx_sig)%r / (2^k)%r) %% 2 = 0) {
        index <- get_tree_index address;
        address <- set_tree_index address (index %/ 2);

        auth_k <- nth witness auth k;
        nodes1 <- rand_hash nodes0 auth_k _seed address;
      } else {
        index <- get_tree_index address;
        address <- set_tree_index address ((index - 1) %/ 2);

        auth_k <- nth witness auth k;
        nodes1 <- rand_hash auth_k nodes0 _seed address;
      }

      nodes0 <- nodes1;
      k <- k+1;
    }

    return nodes0;
  }

  proc verify(pk : xmss_pk, m : msg_t, s : sig_t) : bool = {
    var is_valid : bool;
    var idx_sig : W32.t <- s.`1;
    var idx_bytes : nbytes <- toByte idx_sig n;
    var node, root, _R, _M': nbytes;    
    var auth : auth_path;
    var sig_ots : wots_signature;
    var _seed : seed <- pk.`3;
    var address : adrs <- zero_address;
    var t : three_n_bytes;

    root <- getRootPK pk;
    _R <- s.`2;
    t <- _R ++ root ++ idx_bytes;
    _M' <- H_msg t m;
    
    node <@ rootFromSig(idx_sig, sig_ots, auth, _M', _seed, address);

    is_valid <- (node = root);

    return is_valid;
  }  
}.

(* -------------------------------- MT VARIANT ----------------------------*)

(*
Section 4.2 of the RFC

XMSS^MT uses a tree of several layers of XMSS trees, a so-called hypertree. The
trees on top and intermediate layers are used to sign the root nodes of the trees on the respective layer below. Trees on the lowest layer are used to sign the actual messages. All XMSS trees have equal height.
 *)

(* (wots_sk list) list => We have a wots_sk_list for each XMSS tree *)
type reduced_sk = wots_sk list.
type xmss_mt_sk = W32.t * (reduced_sk list) list * nbytes * nbytes * nbytes.
type xmss_mt_pk = oid * nbytes * nbytes.
type xmss_mt_keypair = xmss_mt_sk * xmss_mt_pk.
type reduced_sig = wots_signature * auth_path.
type sig_mt = W32.t * nbytes * reduced_sig list.

op getXMSS_sk (sk : xmss_mt_sk) (tree layer : int) : reduced_sk =
  let tree_keys : reduced_sk list = nth witness sk.`2 tree in
  nth witness tree_keys layer.

op setXMSS_SK (sk : xmss_mt_sk) (w_sk : reduced_sk) (tree layer : int) : xmss_mt_sk =
   let tree_keys : reduced_sk list = nth witness sk.`2 tree in
   let new_tree_keys : reduced_sk list = put tree_keys layer w_sk in
   let t : reduced_sk list list = put sk.`2 tree new_tree_keys in
   (sk.`1, t, sk.`3, sk.`4, sk.`5).

op xmss_sk_of_reduced_sk (r : reduced_sk) (idx : W32.t) (sk_prf : nbytes) (root : nbytes) (seed : nbytes) : xmss_sk = (idx, r, sk_prf, root, seed).

op getIdx_mt (sk : xmss_mt_sk) : W32.t = sk.`1.
op setIdx_mt (sk : xmss_mt_sk, idx : W32.t) : xmss_mt_sk = (idx, sk.`2, sk.`3, sk.`4, sk.`5).
op getSK_PRF_mt (sk : xmss_mt_sk) : nbytes = sk.`3.
op getRoot_mt (sk : xmss_mt_sk) : nbytes = sk.`4.
op get_seed_mt (sk : xmss_mt_sk) : nbytes = sk.`5.
op setSigIdx (idx : W32.t) (sig : sig_mt) : sig_mt = (idx, sig.`2, sig.`3).

(* gets the n most significant bits *)
op msb (x : byte list) (n : int) : byte list = take n x. 

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

op append_sig (sig : sig_mt) (sig_tmp : reduced_sig) : sig_mt =
    let new_sigs: reduced_sig list = sig.`3  ++  [sig_tmp] in
    (sig.`1, sig.`2, new_sigs).

op getXMSSSignature(sig : sig_mt) (i : int) : reduced_sig = nth witness sig.`3 i.

module XMSS_MT = {
  proc kg() : xmss_mt_keypair = {
    var idx_MT : W32.t <- W32.zero;
    var sk_prf : nbytes;
    var root : nbytes;
    var _seed : seed;
    var layer : int <- 0;
    var tree : int;
    var address : adrs;
    var i : int;
    var ots_sk : wots_sk <- witness;
    var ots_keys : wots_ots_keys <- witness;
    
    var sk : xmss_sk <- witness;
    var reduced_k : reduced_sk <- witness;
    var sk_mt : xmss_mt_sk <- witness;
    var pk : xmss_mt_pk <- witness;

    sk_prf <$ DList.dlist W8.dword n;
    _seed <$ DList.dlist W8.dword n;

    address <- zero_address;

    while (layer < d) {
      address <- set_layer_addr address layer;
      
      tree <- 0;
      while (tree < (1 `<<` ((d - 1 - layer) * (h %/ d)))) {
        address <- set_tree_addr address tree;
        
        i <- 0;
        while (i < 2 ^ (h %/ d)) { (* 2^(h/d) is the height of the current tree *)
            ots_sk <@ WOTS.genSK();
            ots_keys <- put ots_keys i ots_sk;
            i <- i + 1;
        }
        
        (* setXMSS_SK(SK_MT, wots_sk, tree, layer); *)
        sk_mt <- setXMSS_SK sk_mt ots_keys tree layer;
        
        tree <- tree + 1;
      }
      
      layer <- layer + 1;
    }

    (* SK = getXMSS_SK(SK_MT, 0, d - 1); *)
    (* The root field is not used so we can pass witness *)
    reduced_k <- getXMSS_sk sk_mt 0 (d - 1);
    sk <- xmss_sk_of_reduced_sk reduced_k idx_MT sk_prf witness _seed;

    address <- zero_address;
    root <@ TreeHash.treehash(sk, 0, h %/ d, address);

    sk <- (idx_MT, ots_keys, sk_prf, root, _seed);
    pk <- (_oid, root, _seed);
    return (sk_mt, pk);
  }

  proc sign(sk : xmss_mt_sk, m : msg_t) : sig_mt * xmss_mt_sk = {
    var sk_xmss : xmss_sk;
    var idx : W32.t <-getIdx_mt sk;
    var idx_new : W32.t;
    var address : adrs <- zero_address;
    var sig : sig_mt;
    var _R : nbytes;
    var _M' : nbytes;
    var root : nbytes;
    var t : three_n_bytes;
    var idx_bytes : byte list;
    var idx_nbytes : nbytes;
    var idx_tree : W32.t;
    var idx_leaf : W32.t;
    var sk_prf : nbytes <- getSK_PRF_mt sk;
    var seed : nbytes <- get_seed_mt sk;
    var sig_tmp : wots_signature;
    var auth : auth_path;
    var reduced_k : reduced_sk <- witness;
    var j : int;

    
    (* Update SK_MT *)
    idx_new <- idx + W32.one;
    sk <- setIdx_mt sk idx_new;

    idx_bytes <- toByte idx 32;
    _R <- _prf_ sk_prf idx_bytes;

    idx_nbytes <- toByte idx n;
    root <- getRoot_mt sk;
    t <- _R ++ root ++ idx_nbytes;
    _M' <- H_msg t m;

    idx_tree <- msb_w32_int idx (h - (h %/ d));
    idx_leaf <- msb_w32_int idx (h %/ d);
    
    reduced_k <- getXMSS_sk sk (W32.to_uint idx_tree) 0;
    sk_xmss <- (idx_leaf, reduced_k, sk_prf, toByte W32.zero n, seed);

    address <- set_layer_addr address 0;
    address <- set_tree_addr address (W32.to_uint idx_tree);

    (sig_tmp, auth) <@ TreeSig.treesig(_M', sk_xmss, idx_leaf, address);

    sig <- (idx, _R, [(sig_tmp, auth)]);

    j <- 1;
    while (j < d) {
      root <@ TreeHash.treehash(sk_xmss, 0, h %/ d, address);
      idx_leaf <- lsb_w32_int idx_tree (h %/ d);
      idx_tree <- msb_w32_int idx_tree (h - (j * (h %/ d)));
      
      reduced_k <- getXMSS_sk sk (W32.to_uint idx_tree) j;
      sk_xmss <- (idx_leaf, reduced_k, sk_prf, toByte W32.zero n, seed);

      address <- set_layer_addr address j;
      address <- set_tree_addr address (W32.to_uint idx_tree);

      (sig_tmp, auth) <@ TreeSig.treesig(root, sk_xmss, idx_leaf, address);
      
      sig <- append_sig sig (sig_tmp, auth);
      
      
      j <- j+1;
    }

    return (sig, sk);
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

  proc verify(pk : xmss_mt_pk, m : msg_t, s : sig_mt) : bool = {
    var is_valid : bool;
    var idx : W32.t <- s.`1;
    var idx_bytes : nbytes <- toByte idx n;
    var seed : nbytes <- pk.`3;
    var address : adrs <- zero_address;
    var idx_leaf : W32.t <- lsb_w32_int idx (h %/ d);
    var idx_tree : W32.t <- msb_w32_int idx (h - (h %/ d));
    var _sig : reduced_sig;
    var node, root, _R, _M': nbytes;
    var t : three_n_bytes;
    var j : int;

    _sig <- getXMSSSignature s 0;

    _R <- s.`2;
    root <- pk.`2;
    t <- _R ++ root ++ idx_bytes;
    _M' <- H_msg t m;

    address <- set_layer_addr address 0;
    address <- set_tree_addr address (W32.to_uint idx_tree);
    
    node <@ XMSS.rootFromSig(idx_leaf, _sig.`1, _sig.`2, _M', seed, address);

    j <- 1;
    while (j < d) {
      idx_leaf <- lsb_w32_int idx_tree (h %/ d);
      idx_tree <- msb_w32_int idx_tree (h - (h %/ d));

      _sig <- getXMSSSignature s j;
      
      address <- set_layer_addr address j;
      address <- set_tree_addr address (W32.to_uint idx_tree);

      node <@ XMSS.rootFromSig(idx_leaf, _sig.`1, _sig.`2, _M', seed, address);

      j <- j + 1;
    }

    is_valid <- (node = root);

    return is_valid;
  }
}.

(*******************************************************************************)
(*                   If d = 1, XMSS^MT = XMSS                                  *)
(*******************************************************************************)