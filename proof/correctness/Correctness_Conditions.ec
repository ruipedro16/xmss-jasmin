pragma Goals : printall.

require import AllCore.
from Jasmin require import JModel.
require import XMSS_IMPL.

(* CPU FLAGS : of, cf, sf, pf, zf *)

require import Array11.

lemma neg_impl (p : bool) : !p <=> (p => false) by smt().
lemma not_b_implies_b_false (b : bool) : !b => b = false by smt().
lemma false_neq (a b : W8.t) : (a <> b) => ((a = b) = false) by move => ?; apply not_b_implies_b_false.

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

lemma treehash_condition_correct_eq (h : W32.t Array11.t) (o : W64.t) :
    hoare [
    M(Syscall).__treehash_cond :
    0 <= to_uint o <= W32.max_uint /\
    arg = (h, o) 
    ==>
    (res = W8.one) = treehash_cond h o
    ].
proof.
proc => /=.
seq 3 : (#pre /\ bc1 = if (2 <= to_uint offset) then W8.one else W8.zero). 
  + auto => /> *.
    case (2 <= to_uint o) => H; [rewrite setcc_true | rewrite setcc_false] => //; rewrite cmp_eq_W64 cmp_lt_W64 /_uGE /_uLT; [smt(@W64) |].
    rewrite ultE of_uintK // #smt(@W64).
if.
- (* 1st branch: bc1 = W8.zero i.e 2 <= offset is false so the whole expression is false *)
   auto => /> ???.
   rewrite /treehash_cond.
   have ->: 2 <= to_uint o = false by smt(@W8).
   simplify.
   have E: W8.zero <> W8.one by smt(@W8).
   have ->: (W8.zero = W8.one) = false by apply false_neq; assumption.
   trivial.
- (* 2nd branch: bc1 = W8.zero i.e. 2 <= offset is true *)
   auto => /> *.
   have E: 2 <= to_uint o by smt().
   rewrite /treehash_cond /=.
   have ->: 2 <= to_uint o = true by smt().
   simplify.
   rewrite /_EQ cmp_eq_W32 !to_uintB; 1,2: by rewrite uleE /#.
   rewrite of_uintK /= /#.
qed.

lemma treehash_condition_correct_equiv (h : W32.t Array11.t) (o : W64.t) :
    hoare [
    M(Syscall).__treehash_cond :
    0 <= to_uint o <= W32.max_uint /\
    arg = (h, o) 
    ==>
    (res = W8.one) <=> treehash_cond h o
    ].
proof.
conseq (: _ ==> (res = W8.one) = treehash_cond h o); first by auto => /> /#. (* Reuse the proof from before *)
proc => /=.
seq 3 : (#pre /\ bc1 = if (2 <= to_uint offset) then W8.one else W8.zero). 
  + auto => /> *.
    case (2 <= to_uint o) => H; [rewrite setcc_true | rewrite setcc_false] => //; rewrite cmp_eq_W64 cmp_lt_W64 /_uGE /_uLT; [smt(@W64) |].
    rewrite ultE of_uintK // #smt(@W64).
if.
- (* 1st branch: bc1 = W8.zero i.e 2 <= offset is false so the whole expression is false *)
   auto => /> ???.
   rewrite /treehash_cond.
   have ->: 2 <= to_uint o = false by smt(@W8).
   simplify.
   have E: W8.zero <> W8.one by smt(@W8).
   have ->: (W8.zero = W8.one) = false by apply false_neq; assumption.
   trivial.
- (* 2nd branch: bc1 = W8.zero i.e. 2 <= offset is true *)
   auto => /> *.
   have E: 2 <= to_uint o by smt().
   rewrite /treehash_cond /=.
   have ->: 2 <= to_uint o = true by smt().
   simplify.
   rewrite /_EQ cmp_eq_W32 !to_uintB; 1,2: by rewrite uleE /#.
   rewrite of_uintK /= /#.
qed.

(* ============================================================================================================================= *)
(* PHOARE VERSION OF THE LEMMAS *)
(* ============================================================================================================================= *)

lemma p_treehash_condition_correct_eq (h : W32.t Array11.t) (o : W64.t) :
    phoare [
    M(Syscall).__treehash_cond :
    0 <= to_uint o <= W32.max_uint /\
    arg = (h, o) 
    ==>
    (res = W8.one) = treehash_cond h o
    ] = 1%r by conseq treehash_cond_ll (treehash_condition_correct_eq h o). 

lemma p_treehash_condition_correct_equiv (h : W32.t Array11.t) (o : W64.t) :
    phoare [
    M(Syscall).__treehash_cond :
    0 <= to_uint o <= W32.max_uint /\
    arg = (h, o) 
    ==>
    (res = W8.one) <=> treehash_cond h o
    ] = 1%r by conseq treehash_cond_ll (treehash_condition_correct_equiv h o).

