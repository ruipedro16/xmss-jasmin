require import AllCore List RealExp IntDiv.
require Subtype. 

from Jasmin require import JModel.

require import Notation Parameters Address Primitives Wots.

import NBytes.

op h : { int | 0 < h } as h.

(* Used to convert a W32.t. to a byte list *)
clone import Subtype as Four_1Bytes with 
   type T = byte list,
   op P = fun l => size l = 2 * n
   rename "T" as "four_bytes"
   proof inhabited by (exists (nseq (2*n) W8.zero);smt(size_nseq ge0_n))
   proof *.

clone import Subtype as Two_NBytes with 
   type T = byte list,
   op P = fun l => size l = 2 * n
   rename "T" as "two_n_bytes"
   proof inhabited by (exists (nseq (2*n) W8.zero);smt(size_nseq ge0_n))
   proof *.


(* for the PK *)
clone import Subtype as Two_NBytes_Plus4 with 
   type T = byte list,
   op P = fun l => size l = 2 * n
   rename "T" as "two_n_bytes_plus_4"
   proof inhabited by admit. (* inhabited by (exists (nseq (2*n + 4) W8.zero);smt(size_nseq ge0_n))
   proof *. => THIS DOESNT WORK*)


(* For the SK *)
clone import Subtype as Two_H_NBytes with 
   type T = skey list,
   op P = fun l => size l = 2^h
   rename "T" as "two_h_nbytes"
   proof inhabited by admit. (* FIXME: *)


clone import Subtype as Three_NBytes with 
   type T = byte list,
   op P = fun l => size l = 3 * n
   rename "T" as "tree_n_bytes"
   proof inhabited by (exists (nseq (3*n) W8.zero);smt(size_nseq ge0_n))
   proof *.



op oid : W32.t.
op oid_to_bytes : W32.t -> four_bytes.
op to_bytes : 'a -> byte list.

op zero_address : adrs.

(*
+---------------------------------+
|          algorithm OID          |     4 bytes
+---------------------------------+
|                                 |
|            root node            |     n bytes
|                                 |
+---------------------------------+
|                                 |
|              SEED               |     n bytes
|                                 |
+---------------------------------+
*)

type pk_t = two_n_bytes_plus_4. 
type sk_t = two_h_nbytes.
type keypair = pk_t * sk_t.

type sig_t = byte list.
type msg_t = byte list.

op bytes_to_sk : byte list -> sk_t.

(* i.e. number of leaves *)
op max_signatures : int = 2^h.

(* XMSS is existentially unforgeable under adaptively chosen message attacks in the
   standard model, provided H is second preimage resistant *)
op H : nbytes -> two_n_bytes -> nbytes.
op H_msg : tree_n_bytes -> byte list -> nbytes.

op get_seed : skey -> seed.

op rand_hash (_left _right : nbytes, _seed : seed, address : adrs) : nbytes = 
  let address : adrs = set_key_and_mask address 0 in
  let key : nbytes = prf _seed address in
  let address : adrs = set_key_and_mask address 1 in
  let bitmask_0 : nbytes = prf _seed address in
  let address : adrs = set_key_and_mask address 2 in
  let bitmask_1 : nbytes = prf _seed address in
  let hash_in : nbytes = (nbytexor _left bitmask_0) ++ (nbytexor _right bitmask_1) in
  H key hash_in.

(* Imperative Definition of XMSS *)
module type SignatureScheme = {
    proc kg() : keypair
    proc sign(sk : sk_t, m : msg_t) : sig_t * sk_t
    proc verify(pk : pk_t, m : msg_t, s : sig_t) : bool
}.

abbrev (>) (a b : int) = b < a. 

module LTree = {
  proc ltree (pk : pkey, address : adrs, _seed : seed) : nbytes = {
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

op remove_last (x : 'a list) : 'a list = 
with x = [] => []
with x = h::t => if t = [] then [] else remove_last t.

abbrev push (x : 'a list) (a : 'a) : 'a list = rcons x a. 
abbrev pop (x : 'a list) : 'a list * 'a = 
    let last_elem : 'a = last witness x in
    let new_list = remove_last x in
    (new_list, last_elem).

op same_height : nbytes -> int -> bool. (* TODO: *)

op set_sk_prf : sk_t -> nbytes -> sk_t. (* TODO: *)
op set_seed : sk_t -> seed -> sk_t.     (* TODO: *)
op set_wots_sk : sk_t -> skey list -> sk_t.  (* TODO: *)

module Treehash = {
  proc treehash(sk : skey, s t : int, address : adrs) : nbytes = {
    var stack : nbytes list;
    var node : nbytes;
    var top_node : nbytes;
    var _seed : seed;
    var pk : pkey;
    var i : int <- 0;
    var tree_index, tree_height: int;

    pk <- witness; (* To suppress warning *)
    stack <- witness; (* FIXME: NOT INITIALIZED *)

    while (i < 2^t) {
      _seed  <- get_seed sk;
      address <- set_type address 0;
      address <- set_ots_addr address (s + 1);
      pk <- genPKWots pk sk _seed address; (* FIXME: s+1?? *)
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
 


(* It is REQUIRED that s % 2^t = 0, i.e., that the leaf at index s is a leftmost leaf of a sub-tree of height t. *)
pred leftmost_leaf (s t : int)  = s %% 2^t = 0.

pred treehash_p (s t : int) = s %% (1 `<<` t) <> 0.

module XMSS : SignatureScheme = {
  proc kg() : keypair = {
    var idx : int;
    var i : int <- 0;
    var pk : pk_t;
    var sk : sk_t;
    var wots_sk : skey list;
    var wots_sk_i : skey;
    var sk_prf : nbytes;
    var _seed : seed;
    var oid_as_bytes : four_bytes;
    var root : nbytes;
    var address : adrs;

    while (i < 2^h) {
      wots_sk_i <@ WOTS.genSK();
      wots_sk <- put wots_sk i wots_sk_i;
      i <- i + 1;
    }

    sk_prf <- sample_n_bytes sk_prf;
    sk <- set_sk_prf sk sk_prf;

    _seed <- sample_n_bytes _seed;
    sk <- set_seed sk _seed;

    sk <- set_wots_sk sk wots_sk;

    address <- zero_address;
    (* root <@ Treehash.treehash(sk, 0, h, address); *) (* FIXME: Wrong type of SK *)
    root <- witness;

    oid_as_bytes <- oid_to_bytes oid;

    sk <- bytes_to_sk ( (to_bytes oid) ++ (to_bytes wots_sk) ++ (to_bytes sk_prf) ++ (to_bytes root) ++ _seed );

    pk <- oid_as_bytes ++ root ++ _seed;


    return (pk, sk);
  }

  proc sign(sk : sk_t, m : msg_t) : sig_t * sk_t = {
    var sig : sig_t <- witness;

    return (sig, sk);
  }

  proc verify(pk : pk_t, m : msg_t, s : sig_t) : bool = {
    var is_valid : bool <- false;

    return is_valid;
  }
}.

(* Functional Definition of XMSS *)
