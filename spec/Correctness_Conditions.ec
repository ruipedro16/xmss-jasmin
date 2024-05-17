pragma Goals : printall.

require import AllCore List RealExp IntDiv.
from Jasmin require import JModel.
require import XMSS_IMPL.


(* cond = a < b /\ a < c *)
lemma cond_u32_a_below_b_and_a_below_c(_a : W32.t, _b : W32.t, _c : W32.t) : 
    hoare[M(Syscall).__cond_u32_a_below_b_and_a_below_c :
      arg = (_a, _b, _c) ==> 
         res = (W32.to_uint _a) < (W32.to_uint _b) /\ (W32.to_uint _a) < (W32.to_uint _c)].
proof.
proc.
auto => />.
admit.
qed.


(* cond = a >= b /\ c == d *)
(* cond = b <= a /\ c = d *)
lemma cond_u64_geq_u64_u32_eq_u32(_a : W64.t, _b : W64.t, _c : W32.t, _d :W32.t) :
    hoare[M(Syscall).__cond_u64_geq_u64_u32_eq_u32 :
      arg = (_a, _b, _c, _d) ==>
        res = (W64.to_uint _b) <= (W64.to_uint _a) /\ (W32.to_uint _c) = (W32.to_uint _d)].
proof.
proc.
auto => />.
admit.
qed.
