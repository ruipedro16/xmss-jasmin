require import AllCore List RealExp IntDiv.
require Subtype. 

from Jasmin require import JModel.

require import Notation Parameters Address Primitives Wots.

import NBytes.
import Array8.

(**********************************************************************************************************************)

clone import Subtype as Bitmask with 
   type T = byte list,
   op P = fun l => size l = 2 * n
   rename "T" as "bitmask"
   proof inhabited by (exists (nseq (2*n) W8.zero);smt(size_nseq ge0_n))
   proof *.

clone import Subtype as Three_NBytes with 
   type T = byte list,
   op P = fun l => size l = 3 * n
   rename "T" as "tree_n_bytes"
   proof inhabited by (exists (nseq (3*n) W8.zero);smt(size_nseq ge0_n))
   proof *.

clone import Subtype as SIG_OTS with 
   type T = nbytes list,
   op P = fun l => size l = len
   rename "T" as "sig_ots"
   proof inhabited by admit.

(**********************************************************************************************************************)

op remove_last (x : 'a list) : 'a list = 
with x = [] => []
with x = h::t => if t = [] then [] else remove_last t.

abbrev push (x : 'a list) (a : 'a) : 'a list = rcons x a. 
abbrev pop (x : 'a list) : 'a list * 'a = 
    let last_elem : 'a = last witness x in
    let new_list = remove_last x in
    (new_list, last_elem).

(**********************************************************************************************************************)

op h : { int | 0 < h } as h.
op max_signatures : int = 2^h.

op H : nbytes -> bitmask -> nbytes.
op H_msg : tree_n_bytes -> byte list -> nbytes.

op oid : W32.t.
op zero_address : adrs = Array8.init (fun _ => W32.zero).

(* Format sk: [OID || (ceil(h/8) bit) idx || SK_SEED || SK_PRF || PUB_SEED || root] *)
type sk_t = W32.t * W32.t * nbytes * nbytes * nbytes * nbytes.

(*
(* Format pk: [OID || root || PUB_SEED] *)
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
*)
type pk_t = W32.t * nbytes * nbytes.

type keypair = pk_t * sk_t.


(*
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
type sig_t = W32.t * nbytes * sig_ots * nbytes list.

type msg_t = byte list.

(**********************************************************************************************************************)

type authentication_path = nbytes list.
op build_authpath : authentication_path.

(**********************************************************************************************************************)

op get_sk_seed (sk : sk_t) : nbytes = sk.`3.
op get_seed (sk : sk_t) : nbytes = sk.`5. (* This is the pub seed *)

(**********************************************************************************************************************)

op rand_hash (_left _right : nbytes, _seed : seed, address : adrs) : nbytes = 
  let address : adrs = set_key_and_mask address 0 in
  let key : nbytes = prf _seed address in
  let address : adrs = set_key_and_mask address 1 in
  let bitmask_0 : nbytes = prf _seed address in
  let address : adrs = set_key_and_mask address 2 in
  let bitmask_1 : nbytes = prf _seed address in
  let hash_in : nbytes = (nbytexor _left bitmask_0) ++ (nbytexor _right bitmask_1) in
  H key hash_in.

(**********************************************************************************************************************)

abbrev (>) (a b : int) = b < a. 

module LTree = {
  proc ltree (pk : wots_pk, address : adrs, _seed : seed) : nbytes = {
    var _len : int <- len;
    var pk_i : nbytes;
    var tmp : nbytes;
    var i : int;

    i <- witness; (* suppress warning *)

    address <- set_tree_height address 0;

    while (_len > 1) {
      i <- 0;
      while (i < floor (len%r / 2%r)) {
        address <-set_tree_index address i;
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

(**********************************************************************************************************************)

(* It is REQUIRED that s % 2^t = 0, i.e., that the leaf at index s is a leftmost leaf of a sub-tree of height t. *)
pred leftmost_leaf (s t : int)  = s %% 2^t = 0.

pred treehash_p (s t : int) = s %% (1 `<<` t) <> 0.

op same_height : nbytes -> int -> bool.

module Treehash = {
  proc treehash(sk : sk_t, s t : int, address : adrs) : nbytes = {
    var stack : nbytes list;
    var node : nbytes;
    var top_node : nbytes;
    var _seed : seed;
    var pk : wots_pk;
    var i : int <- 0;
    var tree_index, tree_height: int;

    pk <- witness; (* To suppress warning *)
    stack <- witness;

    while (i < 2^t) {
      _seed  <- get_seed sk;
      address <- set_type address 0;
      address <- set_ots_addr address (s + 1);
      (*123*)
      (* pk <- genPKWots pk sk _seed address; *)
      address <- set_type address 1;
      address <- set_tree_addr address (s + 1);
      node <@ LTree.ltree(pk, address, _seed); 
      address <- set_type address 2;
      address <- set_tree_height address 0;
      address <- set_tree_index address (i + 1);
      
      top_node <- last witness stack;
      while (same_height top_node t) {
        tree_index <- get_tree_index address;
        address <- set_tree_index address (ceil((tree_index - 1)%r / 2%r));
        (stack, top_node) <- pop stack;
        node <- rand_hash top_node node _seed address;
        
        tree_height <- get_tree_height address;
        address <- set_tree_height address (tree_height + 1);
      }
      stack <- push stack node;

    }

    (stack, node) <- pop stack;
    return node;
  }
}.

(**********************************************************************************************************************)

module AuthPath = {
  proc buildAuth(sk : sk_t, index : int, address : adrs) : authentication_path = {
    var authpath : authentication_path <- witness;
    var j : int <- 0;
    
    while (j < h) {
      j <- j+1;
    }

    return authpath;
  }
}.

op treeSig (m : nbytes, sk : sk_t, index : W32.t, address : adrs) =
  let authpath : authentication_path = witness (* AuthPath.buildAuth(sk, W32.to_uint index, address) *) in
  let address : adrs = set_type address 0 in
  let address : adrs = set_ots_addr address (W32.to_uint index) in
  let sig_ots = witness in
  let sig = sig_ots ++ authpath in
  sig.

(**********************************************************************************************************************)

module type SignatureScheme = {
    proc kg() : keypair
    proc sign(sk : sk_t, m : msg_t) : sig_t * sk_t
    proc verify(pk : pk_t, m : msg_t, s : sig_t) : bool
}.

(*123*)
op nbytes_radndom : nbytes.

module XMSS : SignatureScheme = {
  proc kg() : keypair = {
    var idx : W32.t;
    var i : int <- 0;
    var pk : pk_t;
    var sk : sk_t;
    var wots_skey : wots_sk list;
    var wots_sk_i : wots_sk;
    var sk_prf : nbytes;
    var _seed : seed;
    var root : nbytes;
    var address : adrs;

    while (i < 2^h) {
      wots_sk_i <@ WOTS.genSK();
      wots_skey <- put wots_skey i wots_sk_i;
      i <- i + 1;
    }

    sk_prf <- nbytes_radndom;
    _seed <- nbytes_radndom;
    address <- zero_address;
    root <@ Treehash.treehash(sk, 0, h, address);

    (* Check if this is ok *)
    sk <- (oid, idx, _seed, sk_prf, _seed, root);
    pk <- (oid, root, _seed);

    return (pk, sk);
  }

  proc sign(sk : sk_t, m : msg_t) : sig_t * sk_t = {
    var sig : sig_t <- witness;
    
    var idx_sig : W32.t;

    var address : adrs <- zero_address;

    idx_sig <- sk.`2;

    return (sig, sk);
  }

  proc verify(pk : pk_t, m : msg_t, s : sig_t) : bool = {
    var is_valid : bool <- false;

    return is_valid;
  }
}.
