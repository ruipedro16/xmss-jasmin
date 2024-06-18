pragma Goals : printall.

require import AllCore List RealExp IntDiv.
require import XMSS_IMPL XMSS_IMPL_PP Generic Parameters.

from Jasmin require import JModel.

lemma to_of_int (i : int) : 0 <= i < W64.max_uint => to_uint ((of_int i))%W64 = i by move => ? ; smt(@W64).

lemma memcpy_ll : phoare [ Memcpy._x_memcpy_u8u8 : size in_0 <= 64 ==> true ] = 1%r.
proof.
proc.
while (#pre /\ 0 <= to_uint i <= size in_0) ((size in_0) - (to_uint i)) ; auto => />.
  - move => &hr *. do split.
    + smt(@W64).
    + rewrite to_uintD_small // ; smt(@W64).
    + rewrite to_uintD_small // ; smt(@W64).
  - progress ; [ apply size_ge0 | smt(@W64) ].
qed.

lemma ull_to_bytes_2_ll  : islossless Mp(Syscall).__ull_to_bytes_2 by proc ; while (true) (i - aux) ; by auto => /> /#.
lemma ull_to_bytes_32_ll : islossless Mp(Syscall).__ull_to_bytes_32 by proc ; while (true) (i - aux) ; by auto => /> /#.

lemma zero_addr_ll : islossless Mp(Syscall).__zero_address. 
proof.
proc ; inline *.
auto => />.
while (true) (8 - i) ; by auto => /> /#.
qed.

lemma addr_to_bytes_ll : islossless Mp(Syscall).__addr_to_bytes.
proc.
while (true) (8 - i); last by auto => /> /#.
auto => />.
inline; by auto => /> /#.
qed.

lemma thash_f_ll : islossless Mp(Syscall).__thash_f.
proof.
proc.
auto => />.
while (0 <= to_uint i <= 32) (32 - to_uint i) ; auto => />.
  - auto => /> &hr *. do split ; 1,2: by smt(@W64). rewrite to_uintD_small => /#.
  - auto => /> *. split ; [ progress ; rewrite ultE => /# | auto ].
  - call (addr_to_bytes_ll). inline Mp(Syscall).__set_key_and_mask ; auto => />. 
    call (addr_to_bytes_ll) ; auto => />. 
    call (ull_to_bytes_32_ll). auto => /> i. rewrite ultE /= => * /#.
qed.

(* Base w *)
lemma base_w_ll : phoare [ BaseWGeneric.__base_w : size output <= 67 ==> true ] = 1%r.
proof.
proc.
while (#pre /\ 0 <= to_uint consumed <= size output) ((size output) - (to_uint consumed)) ; auto => />. 
  - progress.
    + rewrite size_put //.
    + smt(@W64).
    + rewrite size_put //. smt(@W64).
    + rewrite size_put to_uintD_small // ; smt(@W64).
    + rewrite size_put //.
    + smt(@W64).
    + rewrite size_put. smt(@W64).
    + rewrite size_put to_uintD_small // ; smt(@W64).
  - progress ; [ apply size_ge0 | smt(@W64) ].
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
auto => /> *.
by rewrite /to_list size_mkseq.
qed.

(* Gen Chain *)
lemma gen_chain_inplace_ll : 
    phoare [ Mp(Syscall).__gen_chain_inplace : 
      0 <= to_uint steps <= XMSS_WOTS_W - 1 ==> 
        true ] = 1%r.
proof.
proc.
auto => />.
while (#pre) ((to_uint steps) - (to_uint i)) ; auto => />.
  - inline Mp(Syscall).__thash_f_ ; inline Mp(Syscall)._thash_f. 
    auto => />. call thash_f_ll. inline Mp(Syscall).__set_hash_addr.
    auto => />.  progress. rewrite to_uintD_small // ; smt(@W32).
  - move => * ; smt(@W32).
qed.

lemma gen_chain_ll : 
    phoare [ Mp(Syscall).__gen_chain :
      0 <= to_uint start <= XMSS_WOTS_W - 1 /\
      0 <= to_uint steps <= XMSS_WOTS_W - 1 /\
      0 <= to_uint (start + steps) <= XMSS_WOTS_W - 1 ==>
        true ] = 1%r.
proc.
auto => /> *.
while (#pre /\ 0 <= to_uint i <= to_uint (start + steps)) ((to_uint t) - (to_uint i)) ; auto => />.
    - call thash_f_ll. inline Mp(Syscall).__set_hash_addr. auto => /> *.
      rewrite to_uintD_small //.
    + smt().
    + do split. 
       * smt().
       * rewrite to_uintD_small //. smt(). move => ?. admit. smt(@W32).
    - progress. smt(@W32). smt(@W32).
    - call memcpy_ptr_ll. skip => />. progress. admit. smt(@W32).
qed.

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
while (true) (67 - i). (* specify the bounds of i here *)
  - auto => />. inline Mp(Syscall).__gen_chain_inplace_ ; inline Mp(Syscall)._gen_chain_inplace ; auto => />.
    call (gen_chain_inplace_ll). inline*.  auto => />. progress ; admit.
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
    call(gen_chain_ll); inline ; auto => />. progress ; by admit.
  - inline Mp(Syscall).__chain_lengths_ ; inline Mp(Syscall)._chain_lengths ; auto => />.
    call (chain_lengths_ll) ; by auto => /> /#.
qed.

(* XMSS *)

lemma ltree_ll : islossless Mp(Syscall).__l_tree. 
proof.
proc.
auto => /> ; call memcpy_ll.
inline Mp(Syscall).__set_tree_height Mp(Syscall).__set_tree_index.
while (0 <= to_uint i <= 67) ((to_uint l) - 1) ; auto => />. (* specify the range of l *)
  - progress. rewrite negb_and. right. rewrite -lezNgt. admit.
  - admit.
  - admit.
qed.

lemma treehash_array_ll : islossless Mp(Syscall).__treehash_array.
proof.
proc.
pose x := 1 `<<` 10.
admit.
qed.
