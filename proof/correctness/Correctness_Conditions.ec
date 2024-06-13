pragma Goals : printall.

require import AllCore.
from Jasmin require import JModel.
require import XMSS_IMPL.

(* CPU FLAGS : of, cf, sf, pf, zf *)

lemma test_8_bool (b1 b2 : bool) :  
  (! (TEST_8 (SETcc b1) (SETcc b2)).`5) = ( b1 /\ b2 ).
proof.
rewrite /SETcc /TEST_8.
case b1.
case b2.
move => ? ? => //=.
smt(@W8).
smt().
move => ? => //=.
qed.

lemma cmp_W64 :
    forall (a b : W64.t), (! (CMP_64 a b).`2) = (b \ule a).
move => a b.
case (b \ule a).
move => ?.
rewrite /CMP_64.
rewrite /rflags_of_aluop => //=.
smt(@W64).
move => ?.
rewrite /CMP_64.
rewrite /rflags_of_aluop => //=.
smt(@W64).
qed.

lemma cmp_eq_W32 :
    forall (a b : W32.t), (CMP_32 a b).`5 = (a = b).
proof.
move => a b.
case (a = b).
move => ?.
rewrite /CMP_32.
rewrite /rflags_of_aluop => //=.
smt(@W32).
move => ?.
rewrite /CMP_32.
rewrite /rflags_of_aluop => //=.
smt(@W32).
qed.

lemma test_cmp_32_64 (_a _b : W64.t) (_c _d : W32.t) :
    (! (TEST_8 (SETcc (! (CMP_64 _a _b).`2)) (SETcc (CMP_32 _c _d).`5)).`5) = ((_b \ule _a) /\ _c = _d).
proof.
rewrite cmp_eq_W32 ; rewrite cmp_W64.
pose b1 := (_b \ule _a).
pose b2 := (_c = _d).
apply test_8_bool.
qed.

(* cond = a >= b /\ c == d *)
(* cond = b <= a /\ c = d *)
lemma cond_u64_geq_u64_u32_eq_u32(_a : W64.t, _b : W64.t, _c : W32.t, _d :W32.t) :
    hoare[M(Syscall).__cond_u64_geq_u64_u32_eq_u32 :
      arg = (_a, _b, _c, _d) ==>
        res = ( _b \ule _a /\ _c = _d )].
proof.
proc.
auto => />.
rewrite /_uGE /_EQ.
rewrite /_uLT /_NEQ.
rewrite /_EQ.
smt(test_cmp_32_64).
qed.
