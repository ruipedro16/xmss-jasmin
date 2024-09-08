pragma Goals : printall.

require import AllCore List RealExp IntDiv.
from Jasmin require import JModel.

require import XMSS_IMPL.
require import Types Address Notation Hash Primitives Params Parameters Utils Util.

require import Array2.

lemma ull_to_bytes_2_correct (y : W64.t) :
    hoare [M(Syscall).__ull_to_bytes_2 : 
      arg.`2 = y ==> 
        to_list res = toByte (W32.of_int (to_uint y)) 2].
proof.
proc.
admit.
qed.

lemma ull_to_bytes_2_ll : islossless M(Syscall).__ull_to_bytes_2
    by proc; while (true) (i - aux); auto => /> /#.

lemma ull_to_bytes_2_equiv (y : W64.t) :
    phoare [M(Syscall).__ull_to_bytes_2 : 
      arg.`2 = y ==> 
        to_list res = toByte (W32.of_int (to_uint y)) 2] = 1%r
          by conseq ull_to_bytes_2_ll (ull_to_bytes_2_correct y) => //.

