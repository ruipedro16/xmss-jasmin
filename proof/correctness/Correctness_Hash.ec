pragma Goals : printall.

require import AllCore List RealExp IntDiv.
from Jasmin require import JModel.

require import XMSS_IMPL_PP XMSS_IMPL.
require import Properties.


lemma ull_tobytes_32_ll : islossless Mp(Syscall).__ull_to_bytes_32
    by proc ; while (true) (i - aux) ; auto => /> /#.

lemma u32_to_bytes_ll : islossless Mp(Syscall).__u32_to_bytes 
    by proc ; islossless.

lemma set_key_and_mask_ll : islossless Mp(Syscall).__set_key_and_mask by islossless.

lemma addr_tobytes_ll : islossless Mp(Syscall).__addr_to_bytes.
proof.
proc.
while (true) (8 - i).
  - auto. call u32_to_bytes_ll. auto => /#.
  - auto => /> /#.
qed.

lemma thash_f_ll : islossless Mp(Syscall).__thash_f.
proof.
proc.
auto => />.
while (0 <= to_uint i <= 32) (32 - to_uint i).
  - auto => /> &hr *. do split.
    + rewrite to_uintD_small /#.
    + move => ? ; smt(@W64).
    + rewrite to_uintD_small /#.
auto => />.
  - progress ;  smt(@W64).
  - call addr_tobytes_ll. call set_key_and_mask_ll. 
    auto => />. call addr_tobytes_ll. call set_key_and_mask_ll.
    auto => />. call ull_tobytes_32_ll. auto => /> * ; smt(@W64).
qed.

require import Array32 Array8.
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
