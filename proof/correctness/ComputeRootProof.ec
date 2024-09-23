pragma Goals : printall.

require import AllCore List RealExp IntDiv Distr DList IntDiv.
from Jasmin require import JModel JArray.

require import Types Params Parameters Address XMSS_MT_TreeHash.
require import XMSS_IMPL.

require import Array32.

lemma computeRootCorrect : 
    equiv [
      M(Syscall).__compute_root ~ RootFromSig.rootFromSig :
      true 
      ==>
      to_list res{1}.`1 = val res{2}
    ].
proof.
proc.
seq 2 0 : #pre; first by auto.
admit.
qed.
