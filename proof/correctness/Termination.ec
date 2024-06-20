pragma Goals : printall.

require import AllCore List RealExp IntDiv.
require import XMSS_IMPL XMSS_IMPL_PP Generic Parameters.

from Jasmin require import JModel.

lemma ull_to_bytes_2_ll  : islossless Mp(Syscall).__ull_to_bytes_2 
    by proc ; while (true) (i - aux) ; by auto => /> /#.

lemma ull_to_bytes_32_ll : islossless Mp(Syscall).__ull_to_bytes_32 
    by proc ; while (true) (i - aux) ; by auto => /> /#.

lemma addr_to_bytes_ll : islossless Mp(Syscall).__addr_to_bytes.
proc.
while (true) (8 - i); last by auto => /> /#.
auto => />.
inline; by auto => /> /#.
qed.

lemma zero_addr_ll : islossless Mp(Syscall).__zero_address_
    by proc ; inline ; wp ; while (true) (8 - i) ; auto => /> /#.

lemma thash_f_ll : islossless Mp(Syscall).__thash_f.
proof.
proc.
auto => />.
while (0 <= to_uint i <= 32) (32 - to_uint i) ; auto => />.
  - auto => /> &hr *. do split ; 1,2: by smt(@W64). rewrite to_uintD_small => /#.
  - auto => /> *. split ; [ progress ; rewrite ultE => /# | auto ].
  - call (addr_to_bytes_ll). inline Mp(Syscall).__set_key_and_mask ; auto => />. 
    call (addr_to_bytes_ll) ; auto => />. 
    call (ull_to_bytes_32_ll). auto => /> *. rewrite ultE => /#.
qed.

lemma base_w_ll : phoare [BaseWGeneric.__base_w : size output <= 67 ==> true] = 1%r.
proof.
proc.
wp.
while (#pre /\ 0 <= to_uint i <= size output) ((size output) - (to_uint i)) ; auto => /> *.
- do split.
  + rewrite size_put /#.
  + rewrite to_uintD_small /#.
  + rewrite size_put ; smt(@W64).
  + rewrite size_put to_uintD_small ; smt(@W64).
  + move => ? ; do split.
    * rewrite size_put /#.
    * rewrite to_uintD_small /#.
    * move => ? ; rewrite size_put ; smt(@W64).
    * rewrite size_put to_uintD_small /#.
- split.
  + apply size_ge0.
  + move => * ; rewrite ultE of_uintK /#.
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
lemma gen_chain_inplace_ll : phoare[Mp(Syscall).__gen_chain_inplace : 
    0 <= to_uint steps <= XMSS_WOTS_W ==> true] = 1%r.
proof.
proc.
while (#pre /\ 0 <= to_uint i <= to_uint  steps) ((to_uint steps) - (to_uint i)) ; auto => />.
- inline Mp(Syscall).__thash_f_ Mp(Syscall)._thash_f  Mp(Syscall).__set_hash_addr. wp. call thash_f_ll. 
  auto => /> * ; do split ; by rewrite to_uintD_small /#.
- smt(@W64).
qed.

lemma gen_chain_ll : phoare [Mp(Syscall).__gen_chain :
    0 <= to_uint start <= XMSS_WOTS_W - 1 /\
    0 <= to_uint steps <= XMSS_WOTS_W - 1 /\
    0 <= to_uint (start + steps) <= XMSS_WOTS_W - 1 ==>
      true] = 1%r.
proc.
auto => /> *.
while (#pre /\ 0 <= to_uint i <= to_uint (start + steps) /\ t = start + steps)
      ((to_uint t) - (to_uint i)) ; auto => /> ; 2: by smt(@W32).
- inline Mp(Syscall).__set_hash_addr. call thash_f_ll.
  auto => /> * ; do split ; smt(@W32).
- admit. (* TODO: dont replace memcpyu8u8p *)
qed.

(* Chain Lengths *)
lemma chain_lengths_ll : islossless Mp(Syscall).__chain_lengths.
proof.
proc.
auto => /> ; call (checksum_ll).
auto => /> ; call (base_w_ll).
auto => />.
by rewrite /to_list size_mkseq.
qed.

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

(* Expand Seed *)
lemma expand_seed_ll : islossless Mp(Syscall).__expand_seed.
proof.
proc.
while (true) (67 - i) ; auto => />.
- call (addr_to_bytes_ll). inline. auto => /> /#.
- call memcpy_ll. auto => />. inline*. auto => /> *. split.
  + by rewrite /to_list size_mkseq.
  + smt().
qed.

(* Pk Gen *)
lemma pkgen_ll : islossless Mp(Syscall).__wots_pkgen.
proof.
proc.
while (true) (67 - i).
  - auto => />. inline Mp(Syscall).__gen_chain_inplace_ ; inline Mp(Syscall)._gen_chain_inplace ; auto => />.
    call gen_chain_inplace_ll. inline. auto => /> /#.
  - inline Mp(Syscall).__expand_seed_ Mp(Syscall)._expand_seed ; auto => />.
    call expand_seed_ll ; by auto => /> /#.
qed.

(* Sign *)
lemma wots_sign_ll : islossless Mp(Syscall).__wots_sign.
proof.
proc.
sp ; wp.
while (true) (67 - i).
- auto => />. inline Mp(Syscall).__set_chain_addr ; call gen_chain_inplace_ll ; auto => /> *. do split.
  + smt(@Array67 @W32).
  + admit.
  + admit.
- inline Mp(Syscall).__expand_seed_ Mp(Syscall)._expand_seed.  wp ; call expand_seed_ll.
  inline Mp(Syscall).__chain_lengths_ Mp(Syscall)._chain_lengths. wp ; call chain_lengths_ll.
  auto => /> /#.
qed.

(* Pk from Sig *)
lemma wots_pk_from_sig_ll : islossless Mp(Syscall).__wots_pk_from_sig.
proof.
proc => //=.
while (true) (67 - i).
- auto => />. inline Mp(Syscall).__gen_chain_ ; inline Mp(Syscall)._gen_chain Mp(Syscall).__set_chain_addr ; auto => />.
  call gen_chain_ll. auto => /> *. do split.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
- inline Mp(Syscall).__chain_lengths_ ; inline Mp(Syscall)._chain_lengths ; auto => />.
  call chain_lengths_ll ; by auto => /> /#.
qed.


(* XMSS *)

lemma ltree_ll : islossless Mp(Syscall).__l_tree by admit.

lemma treehash_array_ll : islossless Mp(Syscall).__treehash_array.
proof.
proc.
inline Mp(Syscall).__copy_subtree_addr Mp(Syscall).__set_type Mp(Syscall).__set_ltree_addr Mp(Syscall).__set_ots_addr.
wp ; sp.
while (0 <= j <= 32) (32 - j) ; first by auto => /> /#.
inline Mp(Syscall).__cond_u64_geq_u64_u32_eq_u32. wp.
while (0 <= j <= 32) (32 - j).
- admit.
- admit.
qed.
