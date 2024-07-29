pragma Goals : printall.

require import AllCore List RealExp IntDiv.
require import RandomBytes XMSS_IMPL XMSS_IMPL_HOP1 Parameters.

from Jasmin require import JModel.

require import Array67.

lemma ull_to_bytes_32_ll : islossless M(Syscall).__ull_to_bytes_32 
    by proc ; while (true) (i - aux) ; by auto => /> /#.

lemma _x_memcpy_u8u8_32_32_ll : islossless M(Syscall)._x_memcpy_u8u8_32_32.
proof.
proc; inline*.
auto => />.
while (0 <= to_uint i <= 32) (32 - to_uint i).
  + auto => /> &hr *; do split; smt(@W64 pow2_64).
  + auto => />; smt(@W64).
qed.

lemma _x_memcpy_u8u8_64_64_ll : islossless M(Syscall)._x_memcpy_u8u8_64_64.
proof.
proc; inline*.
wp.
while (0 <= to_uint i <= 64) (64 - to_uint i); auto => /> *; smt(@W64 pow2_64).
qed.

lemma _x_memcpy_u8u8_64_32_ll: islossless M(Syscall)._x_memcpy_u8u8_64_32.
proof.
proc; inline*.
wp.
while (0 <= to_uint i <= 32) (32 - to_uint i); auto => /> *; smt(@W64 pow2_64).
qed.

(*** ***)

lemma sha256_96_ll : islossless M(Syscall).__sha256_96.
proof.
proc.
admit.
qed.

lemma sha256_128_ll : islossless M(Syscall).__sha256_128.
proof.
proc.
admit.
qed.

lemma sha256_in_ptr_ll : islossless M(Syscall).__sha256_in_ptr.
proof.
proc.
admit.
qed.

lemma core_hash_96_ll : islossless M(Syscall).__core_hash__96.
proof.
admit.
qed.

lemma core_hash_128_ll : islossless M(Syscall).__core_hash_128 by proc ; call sha256_128_ll.

lemma prf_ll : islossless M(Syscall).__prf.
proof.
proc.
inline M(Syscall).__core_hash_96; wp.
call sha256_96_ll; wp.
call _x_memcpy_u8u8_32_32_ll; wp.
call _x_memcpy_u8u8_32_32_ll; wp.
call ull_to_bytes_32_ll.
by auto.
qed.

lemma prf_keygen_ll : islossless M(Syscall).__prf_keygen.
proof.
proc.
inline M(Syscall).__core_hash__128 M(Syscall)._core_hash_128; wp.
call core_hash_128_ll; wp.
call _x_memcpy_u8u8_64_64_ll; wp.
call _x_memcpy_u8u8_32_32_ll; wp.
call ull_to_bytes_32_ll.
by auto.
qed.

lemma core_hash_ptr_ll : islossless M(Syscall).__core_hash_in_ptr by proc ; call sha256_in_ptr_ll.

(*** ***)

lemma bytes_to_ull_ptr_ll : islossless M(Syscall).__bytes_to_ull_ptr.
proof.
proc.
while (0 <= to_uint i <= 4) (4 - to_uint i) ; auto => /> * ; last by smt(@W64).
do split.
  + rewrite to_uintD /#.
  + smt(@W64).
  + rewrite to_uintD ; smt(@W64).
qed.

lemma bytes_to_ull_ll : islossless M(Syscall).__bytes_to_ull.
proof.
proc.
while (0 <= to_uint i <= 4) (4 - to_uint i); auto => /> *; last by smt(@W64).
do split.
  + rewrite to_uintD /#.
  + smt(@W64).
  + rewrite to_uintD ; smt(@W64).
qed.

lemma ull_to_bytes_2_ll  : islossless M(Syscall).__ull_to_bytes_2 
    by proc ; while (true) (i - aux) ; by auto => /> /#.

lemma addr_to_bytes_ll : islossless M(Syscall).__addr_to_bytes.
proc.
while (true) (8 - i); last by auto => /> /#.
auto => />.
inline; by auto => /> /#.
qed.

lemma zero_addr_ll : islossless M(Syscall).__zero_address_
    by proc ; inline ; wp ; while (true) (8 - i) ; auto => /> /#.

lemma memcpy_32_ptr_ll : islossless M(Syscall).__memcpy_u8pu8_32.
proof.
proc.
while (0 <= to_uint i <= 32) (32 - to_uint i) ; auto => /> *.
- do split.
  + rewrite to_uintD_small /#.
  + smt(@W64).
  + rewrite to_uintD ; smt(@W64).
- smt(@W64).
qed.

lemma memcpy_ptr_ll : islossless M(Syscall).__memcpy_u8u8p.
proof.
proc.
while (0 <= i <= 32) (32 - i); auto => /> /#.
qed.

lemma memcpy_ptr_ptr_ll : islossless M(Syscall).__memcpy_u8pu8p.
proof.
proc.
while (0 <= to_uint i <= to_uint bytes) ((to_uint bytes) - (to_uint i)) ; auto => /> *.
- do split.
  + rewrite to_uintD ; smt(@W64).
  + smt(@W64).
  + smt(@W64).
- smt(@W64).
qed.

lemma memset_zero_ll : islossless M(Syscall).__memset_zero_u8.
proof.
proc.
while (0 <= to_uint i <= 4) (4 - to_uint i) ; auto => /> *.
do split.
  + rewrite to_uintD_small /#.
  + smt(@W64).
   + rewrite to_uintD_small ; smt(@W64).
- smt(@W64).
qed.

lemma memset_u8_ptr_ll : phoare [M(Syscall).__memset_u8_ptr : 
    0 <= to_uint inlen < W64.modulus ==> true] = 1%r.
proof.
proc.
while (0 <= to_uint i <= to_uint inlen) ((to_uint inlen) - (to_uint i)) ; auto => /> ; progress ; smt(@W64).
qed.

lemma memset_4_ll : islossless M(Syscall).__memset_u8_4.
proof.
proc.
while (0 <= to_uint i <= 4) (4 - to_uint i); auto => /> *; last by smt(@W64).
do split ; [rewrite to_uintD /# | smt(@W64) | rewrite to_uintD ; smt(@W64)].
qed.

lemma memset_128_ll : islossless M(Syscall).__memset_u8_128.
proof.
proc.
while (0 <= to_uint i <= 128) (128 - to_uint i); auto => /> *; last by smt(@W64).
do split ; [rewrite to_uintD /# | smt(@W64) | rewrite to_uintD ; smt(@W64)].
qed.

lemma memcmp_ll : islossless M(Syscall).__memcmp.
proof.
proc.
sp ; wp.
while (0 <= to_uint i <= 32) (32 - to_uint i) ; auto => />.
- progress.
  + rewrite to_uintD_small /#.
  + smt(@W64).
  + rewrite to_uintD ; smt(@W64).
- progress ; smt(@W64).
qed.

lemma thash_f_ll : islossless M(Syscall).__thash_f.
proof.
proc.
auto => />.
wp ; sp.
call core_hash_96_ll.
while (0 <= to_uint i <= 32) (32 - to_uint i) ; auto => />.
  - auto => /> *. do split ; 1,2: by smt(@W64). rewrite to_uintD_small => /#.
  - auto => /> *. split ; [ progress ; rewrite ultE => /# | auto ].
  - inline M(Syscall).__prf_  M(Syscall)._prf; wp. call prf_ll; wp.
    call addr_to_bytes_ll. inline M(Syscall).__set_key_and_mask ; auto => />. 
    inline M(Syscall).__prf_  M(Syscall)._prf; wp. call prf_ll; wp.
call addr_to_bytes_ll ; auto => />. 
    call ull_to_bytes_32_ll. auto => /> *. rewrite ultE => /#.
qed.

lemma thash_h_ll : islossless M(Syscall).__thash_h.
proof.
proc.
wp.
inline M(Syscall)._core_hash_128; wp; call core_hash_128_ll; wp.
while (0 <= to_uint i <= 2 * 32) ((2*32) - (to_uint i)).
- auto => />. progress.
  + rewrite to_uintD_small /#.
  + smt(@W64).
  + rewrite to_uintD_small ; [smt() | smt(@W64)].
- wp. inline M(Syscall).__prf_ M(Syscall)._prf; wp; call prf_ll; wp.
  do (call addr_to_bytes_ll ; wp). 
  inline M(Syscall).__set_key_and_mask; wp.
  call prf_ll; wp.
  call addr_to_bytes_ll; wp; call prf_ll; wp.
  call addr_to_bytes_ll; wp; call ull_to_bytes_32_ll. 
  auto => /> *. 
  smt(@W64).
qed.



lemma hash_msg_ll : islossless M(Syscall).__hash_message.
proof.
proc.
inline M(Syscall).__core_hash_in_ptr_ M(Syscall)._core_hash_in_ptr; wp; call core_hash_ptr_ll; wp.
inline M(Syscall)._x_memcpy_u8pu8_32 M(Syscall)._memcpy_u8pu8_32 ; wp.
call memcpy_32_ptr_ll ; wp. call ull_to_bytes_32_ll ; wp.
do (call memcpy_32_ptr_ll ; wp). call ull_to_bytes_32_ll ; wp.
by skip.
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

lemma base_w_3_2_ll : islossless M(Syscall).__base_w_3_2.
proof.
proc; wp.
while (0 <= consumed <= 3) (3 - consumed); auto => /> /#.
qed.

lemma base_w_67_32_ll : islossless M(Syscall).__base_w_67_32.
proof.
proc; wp.
while (0 <= consumed <= 67) (67 - consumed); auto => /> /#.
qed.

lemma csum_ll : islossless M(Syscall).__csum.
proof.
proc.
while (0 <= to_uint i <= 64) (64 - to_uint i); auto => />.
  - move => ?. rewrite ultE of_uintK /= => *. rewrite to_uintD_small => /#.
  - move => ?. rewrite ultE => /= /#. 
qed.

lemma checksum_ll : islossless M(Syscall).__wots_checksum.
proof.
proc.
auto => />.
call (base_w_3_2_ll).
call (ull_to_bytes_2_ll).
auto => />.
call (csum_ll).
auto => /> *.
qed.

lemma gen_chain_inplace_ll : phoare[M(Syscall).__gen_chain_inplace : 
    0 <= to_uint steps <= XMSS_WOTS_W ==> true] = 1%r.
proof.
proc.
while (#pre /\ 0 <= to_uint i <= to_uint  steps) ((to_uint steps) - (to_uint i)) ; auto => />; last first.
- admit.
- admit.
qed.

lemma chain_lengths_ll : islossless M(Syscall).__chain_lengths.
proof.
proc ; wp.
call checksum_ll ; wp.
call base_w_67_32_ll ; wp.
skip => /> *.
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

lemma expand_seed_ll : islossless M(Syscall).__expand_seed.
proof.
proc.
while (true) (67 - i) ; auto => />.
  - inline M(Syscall).__prf_keygen_ M(Syscall)._prf_keygen; wp.
    call prf_keygen_ll; wp.
    call (addr_to_bytes_ll). inline. auto => /> /#.
  - call _x_memcpy_u8u8_32_32_ll. inline*; auto => /> /#. 
qed.

lemma pkgen_ll : islossless M(Syscall).__wots_pkgen.
proof.
proc.
while (true) (67 - i).
  - auto => />. inline M(Syscall).__gen_chain_inplace_ ; inline M(Syscall)._gen_chain_inplace ; auto => />.
    call gen_chain_inplace_ll. inline. auto => /> /#.
  - inline M(Syscall).__expand_seed_ M(Syscall)._expand_seed ; auto => />.
    call expand_seed_ll ; by auto => /> /#.
qed.

(* TODO: replace with lemma *)
axiom chain_lengths_post : phoare [M(Syscall).__chain_lengths : true ==> 
  forall (k : int), 0 <= k < 67 => (0 <= (to_uint res.[k]) <= 16) ] = 1%r.    

lemma wots_sign_ll : islossless M(Syscall).__wots_sign.
proof.
proc.
sp ; wp.
while (true) (67 - i).
- auto => />. inline M(Syscall).__set_chain_addr M(Syscall).__gen_chain_inplace_ M(Syscall)._gen_chain_inplace.
  wp; call gen_chain_inplace_ll. auto => /> &hr *. 
  rewrite /XMSS_WOTS_W ; do split.
  + smt(@W32).
  + move => ?.  admit.
  + move => ?? /#.
- inline M(Syscall).__expand_seed_ M(Syscall)._expand_seed ;  wp ; call expand_seed_ll.
  inline M(Syscall).__chain_lengths_ M(Syscall)._chain_lengths ; wp ; call chain_lengths_ll.
  auto => /> /#.
qed.


lemma wots_pk_from_sig_ll : islossless M(Syscall).__wots_pk_from_sig.
proof.
proc => //=.
while (true) (67 - i).
- auto => />. inline M(Syscall).__gen_chain_inplace_ M(Syscall)._gen_chain_inplace M(Syscall).__set_chain_addr ; auto => />.
  call gen_chain_inplace_ll. auto => /> *. admit.
- inline M(Syscall).__chain_lengths_ ; inline M(Syscall)._chain_lengths ; auto => />.
  call chain_lengths_ll ; by auto => /> /#.
qed.

(* XMSS *)

lemma ltree_ll : islossless M(Syscall).__l_tree.
proof.
proc.
inline M(Syscall).__set_tree_height.
wp ; sp ; call _x_memcpy_u8u8_32_32_ll.
while (1 <= to_uint l <= 67) (to_uint l - 1).
- auto. wp ; sp. seq 1 : true;  1,2: by admit.
(*3*)  + sp. if.
       * sp ; wp. while (0 <= j <= 32) (32 - j) ; auto => /> ; first by smt(). progress. smt(@W64). admit. admit. admit.
       * auto ; progress ; by admit. 
(*4*)  + admit.
(*5*)  + auto.
- skip => />. smt(@W64). 
qed.

lemma treehash_array_ll : islossless M(Syscall).__treehash_array.
proof.
proc.
inline M(Syscall).__copy_subtree_addr M(Syscall).__set_type M(Syscall).__set_ltree_addr M(Syscall).__set_ots_addr.
wp ; sp.
while (0 <= j <= 32) (32 - j) ; first by auto => /> /#.
inline M(Syscall).__cond_u64_geq_u64_u32_eq_u32. wp.
while (0 <= j <= 32) (32 - j).
- admit.
- auto => />; first by progress ; 1,3:smt(@W32) ; smt(). do call zero_addr_ll.
  skip => /> * ; do split.
  + admit.
  + admit.
  + move => *. split ; last by smt(). rewrite ultE. move => ???. rewrite of_uintK. admit. (* TODO: no info about idx *)
qed.

lemma gen_leaf_ll : islossless M(Syscall).__gen_leaf_wots.
proof.
proc.
inline M(Syscall).__l_tree_ M(Syscall)._l_tree ; wp ; call ltree_ll.
wp ; call pkgen_ll ; wp. 
by skip.
qed.

lemma compute_root_ll : islossless M(Syscall).__compute_root.
proof.
proc.
inline M(Syscall).__set_tree_height M(Syscall).__set_tree_index.
call thash_h_ll. wp.
while (0 <= to_uint i <= (10 - 1)) ((10 - 1) - (to_uint  i)).
- auto => />. wp; sp. if.
  + wp. inline M(Syscall)._x_memcpy_u8u8p M(Syscall)._memcpy_u8u8p.
    wp. call memcpy_ptr_ll. wp ; call thash_h_ll. auto => /> *. smt(@W64 pow2_64). 
  + wp ; inline M(Syscall)._x_memcpy_u8u8p M(Syscall)._memcpy_u8u8p.
    wp; call memcpy_ptr_ll. wp ; call thash_h_ll. auto => /> *. smt(@W64 pow2_64). 
- wp; sp. if.
  + wp. inline M(Syscall)._x_memcpy_u8u8p M(Syscall)._memcpy_u8u8p. wp. call memcpy_ptr_ll.
    wp. call _x_memcpy_u8u8_32_32_ll. skip => /> *. smt(@W64).
  + wp. inline M(Syscall)._x_memcpy_u8u8p M(Syscall)._memcpy_u8u8p; wp; call memcpy_ptr_ll.
    wp. call _x_memcpy_u8u8_64_32_ll. skip => /> *. smt(@W64).
qed.

lemma keypair_seed_ll : islossless M(Syscall).__xmssmt_core_seed_keypair.
proof.
proc.
while (0 <= i <= 32) (32 - i) ; first by auto => /> /#.
wp.
while (0 <= i <= 32) (32 - i) ; first by auto => /> /#.
inline M(Syscall).__treehash_array_ M(Syscall)._treehash_array.
wp ; call treehash_array_ll.
do (wp ; call _x_memcpy_u8u8_32_32_ll).
wp. call _x_memcpy_u8u8_64_64_ll.
wp. call memset_zero_ll. 
inline M(Syscall).__set_layer_addr.
wp ; sp. call zero_addr_ll.
skip ; progress; by smt(@List @Array96 @Array64 @Array32).
qed.

lemma randombytes_ll : islossless Syscall.randombytes_96 by proc ; islossless; smt(@W8 @Distr @DList).

lemma keypair_ll : islossless M(Syscall).__xmssmt_core_keypair.
proof.
proc.
call keypair_seed_ll ; call randombytes_ll.
by auto.
qed.

lemma set_result_ll : phoare [M(Syscall).__set_result :
      0 <= to_uint (loadW64 Glob.mem (to_uint mlen_ptr)) < W64.max_uint ==> true] = 1%r.
proof.
proc.
if.
- wp; call memset_u8_ptr_ll. auto => /> /#.
- inline M(Syscall)._x__memcpy_u8pu8p M(Syscall)._memcpy_u8pu8p ; wp.
  call memcpy_ptr_ptr_ll. wp ; skip => /> *.
qed.

lemma sign_open_ll : phoare [M(Syscall).__xmssmt_core_sign_open :
    0 <= to_uint (loadW64 Glob.mem (to_uint mlen_ptr)) < W64.max_uint ==>
    true] = 1%r.
proof.
proc.
wp ; sp.
inline M(Syscall).__set_type M(Syscall).__set_layer_addr M(Syscall).__set_tree_addr 
       M(Syscall).__set_ots_addr M(Syscall).__set_ltree_addr.
sp ; wp.
call set_result_ll. call memcmp_ll.
while (0 <= to_uint i <= 1) (1 - to_uint i); auto => />.
  + inline M(Syscall).__compute_root_ M(Syscall)._compute_root ; wp ; call compute_root_ll ; wp.
    inline M(Syscall).__l_tree_ M(Syscall)._l_tree ; wp ; call ltree_ll ; wp.
    inline M(Syscall).__wots_pk_from_sig_ ; wp ; call wots_pk_from_sig_ll ; wp. skip => /> *. smt(@W32 pow2_32).
  + progress ; smt(@W32). 
  + call hash_msg_ll. inline M(Syscall)._x_memcpy_u8u8p M(Syscall)._memcpy_u8u8p ; wp.
    call memcpy_ptr_ll ; wp. inline M(Syscall)._x__memcpy_u8pu8p M (Syscall)._memcpy_u8pu8p ; wp. 
    call memcpy_ptr_ptr_ll ; wp. call bytes_to_ull_ptr_ll ; wp. do 3! call zero_addr_ll. 
    skip => /> *. progress.
    * smt(@W32).
    * smt.
    * admit.
qed.

lemma sign_ll : islossless M(Syscall).__xmssmt_core_sign.
proof.
proc.
wp ; sp.
admit.
qed.



(******************************* exported functions **********************************)
lemma kg_ll : islossless M(Syscall).xmss_keypair_jazz.
proof.
proc.
inline M(Syscall).__xmss_keypair M(Syscall).__xmssmt_core_keypair_ M(Syscall)._xmssmt_core_keypair.
wp ; sp. call keypair_ll. by skip.
qed.
