pragma Goals : printall.

require import AllCore List Distr RealExp IntDiv.
require (*  *) Subtype.

from Jasmin require import JModel.

require import Params Notation Address Primitives Wots XMSS.
require import XMSS_IMPL.

require import Array8.

import DList.
import NBytes.

(******************************************************* THASH_ *******************************************************)

op thash_f (address : adrs, _seed : seed, t : nbytes) : nbytes =
    let address = set_key_and_mask address 0 in
    let _key = PRF _seed address in
    let address = set_key_and_mask address 1 in
    let bitmask = PRF _seed address in
    F _key (nbytexor t bitmask).

(***************************************************** PRIMITIVES *****************************************************)

op chain(X : nbytes, i s : int, _seed : seed, address : adrs) : nbytes.

(* Definition of the chain operator for s = 0 *)
axiom chain0 (X : nbytes, i s : int, _seed : nbytes, address : adrs) : 
    s = 0 => chain X i s _seed address = X.

axiom chainS (X : nbytes, i s : int, _seed : nbytes, address : adrs) :
    0 < s => chain X i s _seed address =
      let t = chain X i (s - 1) _seed address in 
      let address = set_hash_addr address (i + s - 1) in
      let address = set_key_and_mask address 0 in
      let _key = PRF _seed  address in
      let address = set_key_and_mask address 1 in
      let bitmask = PRF _seed address in
      let t = F _key (nbytexor t bitmask) in
          t.

lemma chain_ll : islossless Chain.chain
  by proc; while (true) (s - chain_count); by auto => /#.

lemma chain_imp_fun (_X : nbytes, _i _s : int, __seed : nbytes, _address : adrs) : 
  chain_pre _X _i _s __seed _address =>
  hoare [ Chain.chain : 
          arg = (_X, _i, _s, __seed, _address) ==>
             res = chain _X _i _s __seed _address].
proof. 
move => pre_cond.
proc => /=.
while(_X = X /\ _i = i /\ _s = s /\ __seed = _seed /\ 
      (forall (k : int), 0 <= k < 6 => _address.[k] = address.[k]) /\ 
      t = chain _X _i chain_count _seed _address /\
      0 <= chain_count <= s); last by auto; smt(chain0).
auto => /> &hr *.
do split; move => *; 1,3,4: by smt(Array8.set_eqiE Array8.set_neqiE).
by rewrite (chainS _ _ (chain_count{hr} + 1) _ _) 1:/# /=;
   congr; congr => /=; [ | congr];
   apply tP => i  ib;
   case (i <> 7); smt(Array8.set_eqiE Array8.set_neqiE).
qed.

(******************************************************************************)
