pragma Goals : printall.

require import AllCore List Distr RealExp IntDiv.

from Jasmin require import JModel.

require import Array8 Array32.

require import Address.
require import XMSS_IMPL.

op zero_addr : adrs = Array8.init (fun _ => W32.zero). 

lemma zero_addr_op_impl (address : adrs) :
    hoare[M(Syscall)._zero_address : true ==> res = zero_addr].
proof.
proc.
while (
  0 <= i <= 8 /\ 
  (forall (k : int), 0 <= k < i => (addr.[k] = W32.zero))
).
    + auto => /> &hr *; do split;1,2:smt().
      move => k??. 
      rewrite get_setE //= /#.
    + auto => /> &hr *; split => [/# |].
      move => addr0 i0 ???. 
      have ->: i0 = 8 by smt(). 
      move => H.
      rewrite /zero_addr tP => j?. 
      rewrite initiE //=.
      apply H => //.
qed.

lemma zero_addr_ll : islossless M(Syscall)._zero_address by proc; while (true) (8 - i); auto => /> /#.

lemma zero_addr_res (address : adrs) :
    phoare[M(Syscall)._zero_address : true ==> res = zero_addr] = 1%r
      by conseq zero_addr_ll (zero_addr_op_impl address) => //=. 

lemma _addr_to_bytes_correctness (x : W32.t Array8.t) : 
    hoare[M(Syscall).__addr_to_bytes : 
        arg.`2 = x ==> to_list res = addr_to_bytes x].
proof.
proc.
admit. 
qed.

lemma addr_to_bytes_ll : islossless M(Syscall).__addr_to_bytes by proc; inline; while (true) (8 - i); auto => /> /#.

lemma addr_to_bytes_correctness (x : W32.t Array8.t) : 
    phoare[M(Syscall).__addr_to_bytes : arg.`2 = x ==> 
      to_list res = addr_to_bytes x] = 1%r.
proof.
proc.
(* conseq addr_to_bytes_ll (_addr_to_bytes_correctness x). *)
admit.
qed.
