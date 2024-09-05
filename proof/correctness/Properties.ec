pragma Goals : printall.

require import AllCore List RealExp IntDiv.

from Jasmin require import JModel JArray.

require import Types Params Parameters Address Notation Primitives Hash Wots Util.
require import XMSS_IMPL.

require import Array2 Array3 Array8 Array32 Array64 Array67 Array96 Array2144.

require import Utils. (* valid ptr predicate & addr_to_bytes & simplify_pow hint *)
require import Correctness_Mem Correctness_Hash. 


require import Termination Repr.

require import BitEncoding.
(*---*) import BitChunking.

(*** sizes ***)

lemma size_prf : hoare[Hash.prf : true ==> size res = n]
    by proc; seq 2 : (#pre); auto => />; smt(size_hash).

lemma size_F : hoare[Hash._F : true ==> size res = n]
    by proc; seq 2: (true); auto => />; smt(size_hash). 

lemma size_prf_kg : hoare [Hash.prf_keygen : true ==> size res = n]
    by proc; seq 2 : (true); auto => />; smt(size_hash).

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
        ==>
        forall (x : int), x \in res => 0 <= x < w
      ].
proof.
have w_val : w = 4 \/ w = 16 by smt(w_vals).
move => [#] ???.
conseq (:_ ==> (forall (k : int), 0 <= k < size res => 0 <= nth witness res k < w)); first by auto => /> *; smt(@List). 
proc.
auto.
seq 6 : (#pre /\ out = 0 /\ size base_w = ol /\ consumed = 0); first by auto => /> *; rewrite size_nseq /#.
while (
  0 < outlen /\
  size base_w = outlen /\
  out = consumed /\
  0 <= consumed <= outlen /\
  (forall (k : int), 0 <= k < consumed => 0 <= nth witness base_w k < w)
); last by auto => /> /#.
if.
(* proof for first subgoal begins here *)
auto => /> &hr *.
do split;2,3:smt(); [ by rewrite size_put |]. 
move => k *.
case (w = 16).
    - move => ?. 
      have ->: w = 2^4 by smt(). 
      have ->: floor (log2 (2 ^ 4)%r) = 4.
        + simplify.
          have ->: 16%r = 2%r ^ 4%r by simplify. (* this uses hint simplify simplify_pow from Utils.ec *)
          rewrite /log2 logK 1,2:/# from_int_floor //.
      split; rewrite nth_put 1:/# and_mod 1:/# shr_div /#. 
    - move => ?.
      have ->: w = 2 ^ 2 by smt(). 
      have ->: floor (log2 (2 ^ 2)%r) = 2.
        + simplify.
          have ->: 4%r = 2%r ^ 2%r by simplify. (* this uses hint simplify simplify_pow from Utils.ec *)
          rewrite /log2 logK 1,2:/# from_int_floor //.
      split; rewrite nth_put 1:/# and_mod 1:/# shr_div /#. 
(* proof for first subgoal ends here *)
auto => /> &hr *.
rewrite size_put.
do split; 1,2:smt().
move => k *.
case (w = 16).
    - move => ?. 
      have ->: w = 2^4 by smt().
      have ->: floor (log2 (2 ^ 4)%r) = 4. 
        + simplify. 
          have ->: 16%r = 2%r ^ 4%r by simplify. (* this uses hint simplify simplify_pow from Utils.ec *)
          rewrite /log2 logK 1,2:/# from_int_floor //.
      split; rewrite nth_put 1:/# and_mod 1:/# shr_div /#.
    - move => ?. 
      have ->: w = 2 ^ 2 by smt(). 
      have ->: floor (log2 (2 ^ 2)%r) = 2.
        + simplify. 
          have ->: 4%r = 2%r ^ 2%r by simplify. (* this uses hint simplify simplify_pow from Utils.ec *)
          rewrite /log2 logK 1,2:/# from_int_floor //.
      split; rewrite nth_put 1:/# and_mod 1:/# shr_div /#. 
qed.

(*** Checksum bounds ***)

(* The checksum is computed over the base w message, so we know that all bytes are withing the range [0, w [ *)

lemma checksum_bounds : 
    len1 = XMSS_WOTS_LEN1 /\ w = XMSS_WOTS_W =>
    hoare [
      WOTS.checksum :
      size m = 64 /\
      forall (x : int), x \in m => 0 <= x < w
      ==>
      0 <= res <= len1 * (w - 1) 
    ].
proof.
rewrite /XMSS_WOTS_LEN1 /XMSS_WOTS_W => [#] len1_val w_val.
proc.
conseq (: 
  size m = 64 /\
  forall (k : int), 0 <= k < 64 => 0 <= nth witness m k < 16
  ==> _
); first by auto => /> *; smt(@List). 
while (
  size m = 64 /\
  (forall (k : int), 0 <= k < 64 => 0 <= nth witness m k < 16) /\
  0 <= i <= 64 /\
  0 <= checksum <= i * (w - 1)
); auto => /> &hr. 
    + move => ? H0 H1 H2 H3 H4 H5; do split.  
       - smt().  
       - smt().  
       - rewrite w_val //= /#. 
       - rewrite w_val //= /#. 
    + move => ? H0 k j.
      rewrite len1_val w_val //= => H2 H3 H4 H5.
      have ->: j = 64 by smt(). 
      smt(). 
qed.

(*** size of wots gen sk ***)
lemma wots_gen_sk_size : hoare [WOTS.pseudorandom_genSK : true ==> size res.`1 = len /\ (forall (t : W8.t list), t \in res.`1 => size t = n)].
proof.
proc.
seq 1 : (size sk = len /\ (forall (t : W8.t list), t \in sk => size t = n)).
  + auto => />. split; [ smt(size_nseq ge0_len) | smt(@List ge0_n) ].
sp.
while (0 <= i <= len /\ #pre); last by auto => /> *; apply ge0_len.
seq 3 : (#pre /\ size sk_i = n).
  + call  size_prf_kg. admit. 
auto => /> *. admit.
qed.
