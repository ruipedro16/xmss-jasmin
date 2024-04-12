require import AllCore List RealExp IntDiv.
require (*  *) Subtype. 
from Jasmin require import JModel.

require import Notation Address.
require import Array8.

type adrs = W32.t Array8.t.

op n : { int | 0 <= n } as ge0_n.

op len1 : int = ceil (8%r * n%r / log2 w%r).
op len2 : int = floor (log2 (len1 * (w - 1))%r / log2 w%r) + 1.
op len : int = len1 + len2.

(* replaced lemma with axiom *)
axiom ge0_len : 0 <= len.

clone import Subtype as NBytes with 
   type T = byte list,
   op P = fun l => size l = n
   rename "T" as "nbytes"
   proof inhabited by (exists (nseq n W8.zero);smt(size_nseq ge0_n))
   proof *.

type key = nbytes.
type seed = nbytes.

op prf : seed -> adrs -> key.
op f : key -> nbytes -> nbytes.

op nbytexor(a b : nbytes) : nbytes = 
    map (fun (ab : byte * byte) => ab.`1 `^` ab.`2) (zip a b).

module Chain = {
  proc chain(X : nbytes, i s : int, _seed : seed, address : adrs) : nbytes = {
    var t : nbytes <- X;
    var _key : key;
    var chain_count : int <- 0;
    var bitmask : nbytes;

    (* case i + s <= w-1 is precondition *)
    while (chain_count < s) {
     address <- set_hash_addr address (i + chain_count);
     address <- set_key_and_mask address 0;
     _key <- prf _seed  address;
     address <- set_key_and_mask address 1;
     bitmask <- prf _seed address;

     t <- f _key (nbytexor t bitmask);
     chain_count <- chain_count + 1;       
    }
    return t;
  }
}.

pred chain_pre(X : nbytes, i s : int, _seed : seed, address : adrs) = 
    0 <= s <= w-1.

op chain(X : nbytes, i s : int, _seed : seed, address : adrs) : nbytes.

(* Definition of the chain operator for s = 0 *)
axiom chain0 (X : nbytes, i s : int, _seed : nbytes, address : adrs) : 
    s = 0 => chain X i s _seed address = X.

axiom chainS (X : nbytes, i s : int, _seed : nbytes, address : adrs) :
    0 < s => chain X i s _seed address =
      let t = chain X i (s - 1) _seed address in 
      let address = set_hash_addr address (i + s - 1) in
      let address = set_key_and_mask address 0 in
      let _key = prf _seed  address in
      let address = set_key_and_mask address 1 in
      let bitmask = prf _seed address in
      let t = f _key (nbytexor t bitmask) in
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
