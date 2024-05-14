pragma Goals : printall.

require import AllCore List RealExp IntDiv.
require import WArray32.

from Jasmin require import JModel_x86.

require import XMSS_IMPL.

(* This is not used anywhere *)
lemma zero_W64 : W64.to_uint(W64.zero) = 0.
proof.
trivial.
qed.

lemma size_ge0_W64 (x : 'a list) : W64.to_uint(W64.zero) <= size x.  
proof.
smt(size_ge0).
qed.

(* Same for WArray *)
