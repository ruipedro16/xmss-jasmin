pragma Goals : printall.

require import AllCore List RealExp IntDiv Distr DList IntDiv.
from Jasmin require import JModel JArray.

require import Types Params Address XMSS_MT_PRF.
require import XMSS_IMPL.

require import Array32.

require import Correctness_Address.

lemma verify_correct mem :
    equiv[
        M(Syscall).__xmssmt_core_sign_open ~ XMSS_MT_PRF.verify : 
        Glob.mem{1} = mem /\
        Glob.mem{2} = mem
        ==> 
        true
].
proof.
proc.
seq 9 0 : #pre; first by auto.

seq 1 0 : (#pre /\ to_uint sm_offset{1} = 0); first by auto.

seq 2 0 : (
  #pre /\
  to_list pub_seed{1} = val pk{2}.`pk_pub_seed
).
    + auto => /> &1 &2.  
      admit.

swap {2} 4 -3.

seq 1 0 : (#pre).
    + auto.

seq 1 1 : (
  #pre /\ 
  ots_addr{1} = zero_address /\
  address{2} = zero_address
).
    + inline {1} M(Syscall).__zero_address_.
      wp; sp.
      ecall {1} (zero_addr_res node_addr{1}).
      auto => />. 

seq 1 0 : (
  #pre /\ 
  ltree_addr{1} = zero_address
).
    + inline {1} M(Syscall).__zero_address_.
      wp; sp.
      ecall {1} (zero_addr_res ltree_addr{1}).
      auto => />.

seq 1 0 : (
  #pre /\ 
  node_addr{1} = zero_address
).
    + inline {1} M(Syscall).__zero_address_.
      wp; sp.
      ecall {1} (zero_addr_res node_addr{1}).
      auto => />.
admit.
qed.
