require import AllCore List RealExp IntDiv.
require Subtype. 

from Jasmin require import JModel.

require import Notation Parameters Address Primitives Wots.

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
   rename "T" as "tree_n_bytes"
   proof inhabited by (exists (nseq (3*n) W8.zero);smt(size_nseq ge0_n))
   proof *.

(*********************************************************************************************)

op h : { int | 0 < h } as h.
op max_signatures : int = 2^h.

(*
Besides the cryptographic hash function F and the pseudorandom
function PRF required by WOTS+, XMSS uses two more functions:

-  A cryptographic hash function H.  H accepts n-byte keys and byte
      strings of length 2n and returns an n-byte string.

-  A cryptographic hash function H_msg.  H_msg accepts 3n-byte keys
      and byte strings of arbitrary length and returns an n-byte string.
 *)
op H : nbytes -> bitmask -> nbytes.
op H_msg : tree_n_bytes -> byte list -> nbytes.

type oid =  W32.t.

(* Format sk: [OID || (ceil(h/8) bit) idx || SK_SEED || SK_PRF || PUB_SEED || root] *)
type sk_t = oid * W32.t * nbytes * nbytes * nbytes * nbytes.

(* Format pk: [OID || root || PUB_SEED] *)
type pk_t = oid * nbytes * nbytes.

type keypair = pk_t * sk_t.

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

    while (_len > 1) {
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

(* TODO: Replace with belast ? *)
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

op same_height : nbytes -> int -> bool. (* TODO: *)


(**************************************************************************************************)

module type SignatureScheme = {
    proc kg() : keypair
    proc sign(sk : sk_t, m : msg_t) : sig_t * sk_t
    proc verify(pk : pk_t, m : msg_t, s : sig_t) : bool
}.
