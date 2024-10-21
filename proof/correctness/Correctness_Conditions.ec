pragma Goals : printall.

require import AllCore.
from Jasmin require import JModel.
require import XMSS_IMPL.

(* CPU FLAGS : of, cf, sf, pf, zf *)

require import Array11.

lemma setcc_false (p : bool) : !p => SETcc p = W8.zero by rewrite /SETcc /#.
lemma setcc_true  (p : bool) :  p => SETcc p = W8.one  by rewrite /SETcc /#.

lemma cmp_eq_W32 :
    forall (a b : W32.t), (CMP_32 a b).`5 = (a = b).
proof.
move => a b.
case (a = b) => ?; rewrite /CMP_32 /rflags_of_aluop //=. 
  + have ->:  (a - b) = W32.zero by smt(@W32).
    smt().
smt(@W32).
qed.

lemma cmp_eq_W64 :
    forall (a b : W64.t), (CMP_64 a b).`5 = (a = b).
proof.
move => a b.
case (a = b) => ?; rewrite /CMP_64 /rflags_of_aluop //=. 
  + have ->:  (a - b) = W64.zero by smt(@W64).
    smt().
smt(@W64).
qed.

lemma cmp_lt_W64 :
    forall (a b : W64.t), (CMP_64 a b).`2 = (a \ult b).
proof.
move => a b.
rewrite /CMP_64 /rflags_of_aluop => />; smt(@W64).
qed.

lemma treehash_cond_ll : islossless M(Syscall).__treehash_cond by proc; auto.

pred treehash_cond (h : W32.t Array11.t) (o : W64.t) = 2 <= to_uint o /\ (h.[to_uint o - 2] = h.[to_uint o -1]).

lemma treehash_cond_correct (h : W32.t Array11.t) (o : W64.t) : 
    hoare [
      M(Syscall).__treehash_cond :
      0 <= to_uint o <= W32.max_uint /\
      arg = (h, o) 
      ==>
      if treehash_cond h o then res = W8.one else res = W8.zero 
    ].
proof.
proc.
seq 3 : (#pre /\ bc1 = if (2 <= to_uint offset) then W8.one else W8.zero).
  + auto => /> *.
    case (2 <= to_uint o) => H; [rewrite setcc_true | rewrite setcc_false] => //; rewrite cmp_eq_W64 cmp_lt_W64 /_uGE /_uLT; [smt(@W64) |].
    rewrite ultE of_uintK // #smt(@W64).
if; first by auto => />.
auto => /> *.
split => *; [rewrite setcc_true | rewrite setcc_false ] => //; rewrite cmp_eq_W32 /_EQ !to_uintB 3:/#; by rewrite uleE /#.        
qed.

(* Same as previous lemma but this one is phoare *)
lemma treehash_cond_correct_p (h : W32.t Array11.t) (o : W64.t) : 
    phoare [
      M(Syscall).__treehash_cond :
      0 <= to_uint o <= W32.max_uint /\
      arg = (h, o) 
      ==>
      if treehash_cond h o then res = W8.one else res = W8.zero 
    ] =1%r by conseq treehash_cond_ll (treehash_cond_correct h o).
