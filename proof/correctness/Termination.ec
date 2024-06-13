pragma Goals : printall.

require import AllCore List RealExp IntDiv.
require import XMSS_IMPL XMSS_IMPL_PP Generic.

from Jasmin require import JModel.

lemma to_of_int (i : int) : 0 <= i < W64.max_uint => to_uint ((of_int i))%W64 = i by move => ? ; smt(@W64).

lemma memcpy_ll : phoare [Memcpy._x_memcpy_u8u8 : 0 <= inlen < W64.max_uint ==> true] = 1%r.
proof.
proc.
while (#pre /\ 0 <= to_uint i <= inlen) (inlen - to_uint i) ; auto => />.
  - move => &hr. rewrite ultE of_uintK //= => *. rewrite to_uintD_small => /#.
  - move => &hr ?????. rewrite ultE //= => *. rewrite to_of_int => /#. 
qed.

lemma ull_to_bytes_2_ll  : islossless Mp(Syscall).__ull_to_bytes_2 by proc ; while (true) (i - aux) ; by auto => /> /#.
lemma ull_to_bytes_32_ll : islossless Mp(Syscall).__ull_to_bytes_32 by proc ; while (true) (i - aux) ; by auto => /> /#.

lemma addr_to_bytes_ll : islossless Mp(Syscall).__addr_to_bytes.
proc.
while (true) (8 - i); last by auto => /> /#.
auto => />.
inline; by auto => /> /#.
qed.

lemma thash_f_ll : islossless Mp(Syscall)._thash_f.
proof.
proc.
inline Mp(Syscall).__thash_f => //=.
auto => />.
while (0 <= to_uint i <= 32) (32 - to_uint i) ; auto => />.
  - auto => /> &hr *. do split ; 1,2: by smt(@W64). rewrite to_uintD_small => /#.
  - auto => /> *. split ; [ progress ; rewrite ultE => /# | auto ].
  - call (addr_to_bytes_ll). inline Mp(Syscall).__set_key_and_mask ; auto => />. 
    call (addr_to_bytes_ll) ; auto => />. 
    call (ull_to_bytes_32_ll). auto => /> i. rewrite ultE /= => * /#.
qed.

(* Base w *)
lemma base_w_ll : islossless BaseWGeneric.__base_w.
proof.
proc.
islossless.
while (true) ((to_uint outlen) - (to_uint consumed)) ; [auto => /> *; smt(@W64) | skip => /> /#].
qed.

lemma csum_ll : islossless Mp(Syscall).__csum.
proof.
proc.
while (0 <= to_uint i <= 64) (64 - to_uint i); auto => />.
  - move => &hr. rewrite ultE of_uintK /= => *. rewrite to_uintD_small => /#.
  - move => ?. rewrite ultE => /= /#. 
qed.

lemma checksum_ll : islossless Mp(Syscall).__wots_checksum.
proof.
proc.
auto => />.
call (base_w_ll).
call (ull_to_bytes_2_ll).
auto => />.
call (csum_ll).
auto => /> .
qed.

(* Gen Chain *)
lemma gen_chain_inplace_ll : islossless Mp(Syscall).__gen_chain_inplace.
proof.
proc.
auto => />.
(*
while (0 <= to_uint i <= to_uint t) ((to_uint t) - (to_uint i)).
  - auto => />. inline Mp(Syscall).__thash_f_ ;  auto => /> ; call(thash_f_ll).
    inline. auto => /> &hr. rewrite ultE. rewrite to_uintD_small => //=. admit. progress. smt(). admit. idtac => //= /#.
  - auto => /> &hr i. rewrite ultE -lezNgt => /#.
*)
admit.
qed.

lemma gen_chain_ll : islossless Mp(Syscall).__gen_chain by admit.

(* Chain Lengths *)
lemma chain_lengths_ll : islossless Mp(Syscall).__chain_lengths.
proof.
proc.
auto => /> ; call (checksum_ll).
auto => /> ; call (base_w_ll).
auto => />.
qed.

(* Expand Seed *)
lemma expand_seed_ll : islossless Mp(Syscall).__expand_seed.
proof.
proc.
while (true) (67 - i) ; auto => />.
  - call (addr_to_bytes_ll). inline. auto => /> /#.
  - call (memcpy_ll). auto => />. inline ; auto => /> /#.
qed.

(* Pk Gen *)
lemma pkgen_ll : islossless Mp(Syscall).__wots_pkgen.
proof.
proc.
while (true) (67 - i).
  - auto => />. inline Mp(Syscall).__gen_chain_inplace_ ; inline Mp(Syscall)._gen_chain_inplace ; auto => />.
    call (gen_chain_inplace_ll). inline. auto => /> /#.
  - inline Mp(Syscall).__expand_seed_.
    inline Mp(Syscall)._expand_seed ; auto => />.
    call(expand_seed_ll) ; by auto => /> /#.
qed.

(* Sign *)
lemma wots_sign_ll : islossless Mp(Syscall).__wots_sign.
proof.
proc.
while (true) (67 - i).
  - auto => />. inline Mp(Syscall).__gen_chain_inplace_ ; inline Mp(Syscall)._gen_chain_inplace ; auto => />.
    call (gen_chain_inplace_ll). inline* ; auto => /> /#.
  - inline Mp(Syscall).__expand_seed_ ; inline Mp(Syscall)._expand_seed ; auto => /> ; call(expand_seed_ll).
    inline Mp(Syscall).__chain_lengths_ ; inline Mp(Syscall)._chain_lengths ; auto => />.
    call(chain_lengths_ll) ; by auto => /> /#.
qed.

(* Pk from Sig *)
lemma wots_pk_from_sig_ll : islossless Mp(Syscall).__wots_pk_from_sig.
proof.
proc => //=.
while (true) (67 - i).
  - auto => />. inline Mp(Syscall).__gen_chain_ ; inline Mp(Syscall)._gen_chain ; auto => />.
    call(gen_chain_ll); by inline ; auto => /> /#.
  - inline Mp(Syscall).__chain_lengths_ ; inline Mp(Syscall)._chain_lengths ; auto => />.
    call (chain_lengths_ll) ; by auto => /> /#.
qed.

