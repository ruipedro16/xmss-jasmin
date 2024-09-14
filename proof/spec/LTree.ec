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
   rename "T" as "wots_keys".

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
      while (i < _len %/ 2) {
        address <- set_tree_index address i;
        pk_i <- nth witness pk (2*i);
        tmp <- nth witness pk (2*i + 1);
        (pk_i, address) <@ Hash.rand_hash (pk_i, tmp, _seed, address);
        pk <- put pk i pk_i;
        i <- i + 1;
      }

      if (_len %% 2 = 1) {
        pk_i <- nth witness pk (_len - 1);
        pk <- put pk (_len %/ 2) pk_i;
      }

      _len <- if _len %% 2 = 0 then _len %/ 2 else _len %/ 2 + 1;

      tree_height <- get_tree_height address;
      address <- set_tree_height address (tree_height + 1);
    }

    pk_i <- nth witness pk 0;

    return (pk_i, address);
  }
}. 


lemma ltree_ll : islossless LTree.ltree.
admitted.
