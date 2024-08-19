pragma Goals : printall.

require import AllCore List Distr RealExp IntDiv.

from Jasmin require import JModel.

require import Array8.

require import Types Address.
require import XMSS_IMPL.

op zero_addr : adrs = Array8.init (fun _ => W32.zero). 

lemma zero_addr_op_impl (address : adrs) :
    hoare[M(Syscall)._zero_address : true ==> res = zero_addr].
proof.
proc.
while (0 <= i <= 8 /\ 
      (forall (k : int), 0 <= k < i => (addr.[k] = W32.zero))); auto => /> ; smt(get_setE tP initiE).
qed.
