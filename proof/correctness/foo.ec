pragma Goals : printall.

require import AllCore.
from Jasmin require import JModel.
require import XMSS_IMPL.

(* CPU FLAGS : of, cf, sf, pf, zf *)

require import Array11.

lemma neg_impl (p : bool) : !p <=> (p => false) by smt().

lemma setcc_false (p : bool) : !p => SETcc p = W8.zero by rewrite /SETcc /#.
lemma setcc_true  (p : bool) :  p => SETcc p = W8.one  by rewrite /SETcc /#.

pred treehash_cond (h : W32.t Array11.t) (o : W64.t) = 2 <= to_uint o /\ (h.[to_uint o - 2] = h.[to_uint o -1]).

lemma treehash_cond_ll : islossless M(Syscall).__treehash_cond by proc; auto.


(* ============================================================================================================================= *)
lemma cmp_eq_W64 :
    forall (a b : W64.t), (CMP_64 a b).`5 = (a = b).
proof.
move => a b.
case (a = b) => ?; rewrite /CMP_64 /rflags_of_aluop //=; last by smt(@W64).
have ->:  (a - b) = W64.zero by smt(@W64).
by auto.
qed.

lemma cmp_lt_W64 :
    forall (a b : W64.t), (CMP_64 a b).`2 = (a \ult b).
proof.
move => a b.
rewrite /CMP_64 /rflags_of_aluop /= #smt:(@W64).
qed.

lemma cmp_eq_W32 :
    forall (a b : W32.t), (CMP_32 a b).`5 = (a = b).
proof.
move => a b.
case (a = b) => ?; rewrite /CMP_32 /rflags_of_aluop //=; last by smt(@W32).
have ->:  (a - b) = W32.zero by smt(@W32).
by auto.
qed.

(* ============================================================================================================================= *)

lemma treehash_condition_correct_l (h : W32.t Array11.t) (o : W64.t) :
    hoare [
    M(Syscall).__treehash_cond :
    0 <= to_uint o <= W32.max_uint /\
    arg = (h, o) 
    ==>
    (res = W8.one) => treehash_cond h o
    ].
proof.
conseq (: _ 
  ==> 
  (res = W8.one => treehash_cond h o) /\ (treehash_cond h o => res = W8.one)
); first by smt().
proc => /=.
seq 3 : (#pre /\ bc1 = if (2 <= to_uint offset) then W8.one else W8.zero).
  + auto => /> *.
    case (2 <= to_uint o) => H; [rewrite setcc_true | rewrite setcc_false] => //; rewrite cmp_eq_W64 cmp_lt_W64 /_uGE /_uLT; [smt(@W64) |].
    rewrite ultE of_uintK // #smt(@W64).
if; first by auto => /> *; smt(@W8).
auto => /> H0 H1 H2.
split; last first.
    + move => ??.
      rewrite setcc_true // /_EQ cmp_eq_W32 to_uintB /=.
        - rewrite uleE /#.
      rewrite to_uintB.
        - rewrite uleE /#.
      rewrite of_uintK /=/#.
    + have E: 2 <= to_uint o by smt().
      rewrite setcc_true. 
         * rewrite /_EQ cmp_eq_W32.
           rewrite to_uintB; [rewrite uleE /# |].
           rewrite to_uintB; [rewrite uleE /# |].
           rewrite of_uintK /=.
           admit.
         * simplify; split => [/# |].
           admit.
qed.
