pragma Goals : printall.


require import AllCore List RealExp IntDiv Distr DList.
require (*--*) Subtype. 

from Jasmin require import JModel.
 
require import Params Address Hash WOTS.
 

op H : nbytes -> nbytes -> nbytes.
op H_msg : threen_bytes -> W8.t list -> nbytes.

clone export Subtype as WOTSKeys with 
   type T = wots_sk list,
   op P = fun l => size l = 2^h
   rename "sT" as "wots_keys".

clone export Subtype as AuthPath with
  type T = nbytes list,
  op P = fun l => size l = h
  rename "sT" as "auth_path"
  proof inhabited by (exists (nseq h witness);smt(size_nseq ge0_h))
  proof *.


(* 4.1.5 L-Trees *)
(* takes as input a WOTS+ public key pk and compresses it to a single 
   n-byte value pk[0].
*)
module LTree = {
  proc ltree (pk : wots_pk, address : adrs, _seed : seed) : nbytes * adrs = {
    var pks : nbytes list;
    var pk_i : nbytes;
    var tmp : nbytes;
    var i : int;
    var _len : int;
    var tree_height : int;

    address <- set_tree_height address 0;
    pks <- val pk;

    _len <- len;
    while (1 < _len) { (* Same as _len > 1 *)
      i <- 0;
      while (i < _len %/ 2) {
        address <- set_tree_index address i;
        pk_i <- nth witness pks (2*i);
        tmp <- nth witness pks (2*i + 1);
        (pk_i, address) <@ Hash.rand_hash (pk_i, tmp, _seed, address);
        pks <- put pks i pk_i;
        i <- i + 1;
      }

      if (_len %% 2 = 1) {
        pk_i <- nth witness pks (_len - 1);
        pks <- put pks (_len %/ 2) pk_i;
      }

      _len <- if _len %% 2 = 0 then _len %/ 2 else _len %/ 2 + 1;

      tree_height <- get_tree_height address;
      address <- set_tree_height address (tree_height + 1);
    }

    pk_i <- nth witness pks 0;

    return (pk_i, address);
  }
}. 


(******************************************************************************)

(* Stack operations *)
op push (x : 'a list) (a : 'a) : 'a list = rcons x a. 

op remove_last (x : 'a list) : 'a list = 
with x = [] => []
with x = h::t => if t = [] then [] else remove_last t.

op pop (x : 'a list) : 'a list * 'a = 
    let last_elem = last witness x in
    let new_list = remove_last x in
    (new_list, last_elem).

(******************************************************************************)
