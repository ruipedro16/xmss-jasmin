pragma Goals : printall.

require import AllCore List RealExp IntDiv.
require (*  *) Subtype. 
from Jasmin require import JModel.

require import Params Notation Address Hash.
require import Array8.

clone import Subtype as NBytes with 
   type T = W8.t list,
   op P = fun l => size l = n
   rename "T" as "nbytes"
   proof inhabited by (exists (nseq n W8.zero);smt(size_nseq ge0_n))
   proof *.

type key = nbytes.
type seed = nbytes.

(* The WOTS+ algorithm uses a keyed cryptographic hash function F.  F
   accepts and returns byte strings of length n using keys of length n.
*)
op F : key -> nbytes -> nbytes.

(* WOTS+ uses a pseudorandom function PRF. PRF takes as input an n-byte
   key and a 32-byte index and generates pseudorandom outputs of length
   n.
*)
op PRF : seed -> adrs -> key.

op nbytexor(a b : nbytes) : nbytes = 
    map (fun (ab : W8.t * W8.t) => ab.`1 `^` ab.`2) (zip a b).

module Chain = {
   proc chain(X : nbytes, i s : int, _seed : seed, address : adrs) : nbytes * adrs = {
      (*
       *
       * i: start index
       * s: number of steps
       *
       *)
    var t : nbytes <- X;
    var chain_count : int <- 0;
    var _key : key;
    var bitmask : nbytes;

    (* case i + s <= w-1 is precondition *)
    while (chain_count < s) {
     address <- set_hash_addr address (i + chain_count);
     address <- set_key_and_mask address 0;

     _key <- PRF _seed address;
     address <- set_key_and_mask address 1;
     bitmask <- PRF _seed address;

     t <- F _key (nbytexor t bitmask);
     
     chain_count <- chain_count + 1;
    }
    
    return (t, address);
   }
}.

pred chain_pre(X : nbytes, i s : int, _seed : seed, address : adrs) = 
    0 <= s <= w-1.
