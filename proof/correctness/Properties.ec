pragma Goals : printall.

require import AllCore List RealExp IntDiv.
from Jasmin require import JModel JArray.

require import Types Params Parameters Address Notation Primitives Hash Wots Util.
require import XMSS_IMPL.

require import Array2 Array3 Array8 Array32 Array64 Array67 Array96 Array2144.

require import Utils. (* valid ptr predicate & addr_to_bytes *)
require import Correctness_Mem Correctness_Hash. 
(*---*) import NBytes.

require import Termination Repr.

require import BitEncoding.
(*---*) import BitChunking.

(*** sizes ***)

lemma size_prf : hoare[Hash.prf : true ==> size res = n]
    by proc; seq 2 : (#pre); auto => />; smt(size_hash).

lemma size_F : hoare[Hash._F : true ==> size res = n]
    by proc; seq 2: (true); auto => />; smt(size_hash). 

lemma size_chain : hoare[Chain.chain : size X = n ==> size res.`1 = n].
proof.
proc.
sp.
wp.
while (size t = n); last by auto => />.  
seq 3 : (#pre). auto. 
seq 3 : (#pre /\ size _key = n).
  + auto => />. call size_prf. skip => />.
seq 1 : (#pre /\ size bitmask = n). 
  + auto => />. call size_prf. skip => />.
auto => />. 
call size_F.
skip => />. 
qed.

lemma ssize_chain : phoare[Chain.chain : size X = n ==> size res.`1 = n] = 1%r 
    by conseq chain_ll size_chain; auto => />. 


(*** Base W Bounds ***)

lemma base_w_size (l : int) :
    0 < l => 
    hoare [ BaseW.base_w : arg.`2 = l ==> size res = l].
proof.
move => ?. 
proc.
seq 6 : (#post); first by auto => />; rewrite size_nseq /#. 
while (#pre); last by skip.
if; auto => /> *; by rewrite size_put. 
qed.

lemma base_w_bounds (t : W8.t list) (il ol : int):
    0 < il /\ 0 < ol /\ size t = il =>
    hoare [ 
        BaseW.base_w : 
        arg = (t, ol)
        ==> (*       (forall (k : int), 0 <= k < l => 0 <= nth witness res k < w) *)
        forall (x : int), x \in res => 0 <= x < w
      ].
proof.
move => [#] ???.
conseq (:_ ==> (forall (k : int), 0 <= k < size res => 0 <= nth witness res k < w)); first by auto => /> *; smt(@List). 
proc.
auto.
seq 6 : (#pre /\ out = 0 /\ size base_w = ol /\ consumed = 0); first by auto => /> *; rewrite size_nseq /#.
while (
  0 < outlen /\
  size base_w = ol /\
  out = consumed /\
  0 <= consumed <= outlen /\
  (forall (k : int), 0 <= k < consumed => 0 <= nth witness base_w k < w)
); last first. 
    + auto => /> &hr *;  smt(). 
if.
admit.
auto => /> &hr *. 
rewrite size_put. do split; 1,2:smt(). 
move => k Hk0 Hk1.
split. 
    + rewrite nth_put. split; [smt() |]. admit. case (consumed{hr} = k); admit.
    + rewrite nth_put. split; [smt() |]. admit. case (consumed{hr} = k).
       - move => *. admit.
    + smt(@List). 
qed.
