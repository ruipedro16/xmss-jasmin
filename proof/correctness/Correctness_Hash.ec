pragma Goals : printall.

require import AllCore List RealExp IntDiv.
from Jasmin require import JModel.

require import XMSS_IMPL_PP XMSS_IMPL.
require import Properties.


lemma thash_f_correctness (out:W8.t Array32.t, pub_seed:W8.t Array32.t, addr:W32.t Array8.t) : 
    hoare [ Mp(Syscall).__thash_f : 
            arg = (out, pub_seed, addr) ==> 
            to_list res.`1 = thash_f addr (to_list pub_seed) witness]. 
proof.
proc.
auto => />.
admit.
qed.

(* Axiom about hash96 and F *)
