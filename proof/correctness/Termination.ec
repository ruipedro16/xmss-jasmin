pragma Goals : printall.

require import AllCore List RealExp IntDiv.
require import XMSS_IMPL Parameters.

from Jasmin require import JModel.

require import Array67.

(*****************************************************************************************************)
(*** BYTES & ADDRESS ***)
(*****************************************************************************************************)

lemma ull_to_bytes_32_ll : islossless M(Syscall).__ull_to_bytes_32 
    by proc ; while (true) (i - aux) ; by auto => /> /#.

lemma bytes_to_ull_ptr_ll : islossless M(Syscall).__bytes_to_ull_ptr.
proof.
proc.
while (0 <= to_uint i <= 4) (4 - to_uint i) ; auto => /> * ; smt(@W64 pow2_64).
qed.

lemma bytes_to_ull_ll : islossless M(Syscall).__bytes_to_ull.
proof.
proc.
while (0 <= to_uint i <= 4) (4 - to_uint i); auto => /> *; smt(@W64 pow2_64).
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

(*****************************************************************************************************)
(*** MEMCPY, MEMSET & MEMCMP ***)
(*****************************************************************************************************)

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

lemma memcpy_ptr_ll : islossless M(Syscall).__memcpy_u8u8p.
proof.
proc.
while (0 <= i <= 32) (32 - i); auto => /> /#.
qed.

lemma memcpy_ptr_ptr_ll : islossless M(Syscall).__memcpy_u8pu8p.
proof.
proc.
while (0 <= to_uint i <= to_uint bytes) ((to_uint bytes) - (to_uint i)) ; auto => /> *; smt(@W64).
qed.

lemma memcpy_32_ptr_ll : islossless M(Syscall).__memcpy_u8pu8_32.
proof.
proc.
while (0 <= to_uint i <= 32) (32 - to_uint i) ; auto => /> *; smt(@W64 pow2_64).
qed.

lemma memset_zero_ll : islossless M(Syscall).__memset_zero_u8.
proof.
proc.
while (0 <= to_uint i <= 4) (4 - to_uint i) ; auto => /> *; smt(@W64 pow2_64).
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
while (0 <= to_uint i <= 4) (4 - to_uint i); auto => /> *; smt(@W64 pow2_64).
qed.

lemma memset_128_ll : islossless M(Syscall).__memset_u8_128.
proof.
proc.
while (0 <= to_uint i <= 128) (128 - to_uint i); auto => /> *; smt(@W64 pow2_64).
qed.

lemma memcmp_ll : islossless M(Syscall).__memcmp.
proof.
proc.
sp ; wp.
while (0 <= to_uint i <= 32) (32 - to_uint i) ; auto => />; smt(@W64 pow2_64).
qed.

lemma nbytes_copy_320_352_ll : islossless M(Syscall).__nbytes_copy_offset_320_352
    by proc; while (true) (32 - i); auto => /> /#. 


lemma nbytes_copy_352_32_ll : islossless M(Syscall).__nbytes_copy_offset_352_32
    by proc; while (true) (32 - i); auto => /> /#. 


lemma nbytes_copy_32_352_ll : islossless M(Syscall).__nbytes_copy_offset_32_352
    by proc; while (true) (32 - i); auto => /> /#. 


(*****************************************************************************************************)
(*** SHA 256 & CORE HASH ***)
(*****************************************************************************************************)

(*** Functions of Sha256 ***)

lemma store_ref_array_ll : islossless M(Syscall).__store_ref_array
    by proc; while (true) (8 - i); auto => /> /#.

lemma blocks1_ref_ll : 
    phoare [M(Syscall)._blocks_1_ref : 0 <= to_uint nblocks ==> true] = 1%r.
proof.
proc.
wp; sp.
while (0 <= to_uint i <= to_uint nblocks) (to_uint nblocks - to_uint i); last by auto => /> /#.
auto => />.
inline M(Syscall).__store_H_ref; wp.
while (0 <= to_uint tr <= 64) (64 - to_uint tr).
  + auto => />; inline; islossless; move => &hr *; do split; [smt(@W64) | |]; move => *; rewrite to_uintD;
    have ->: to_uint W64.one = 1 by smt().
    * admit.
    * admit.
inline M(Syscall).__load_H_ref; wp.
while (true) (64 - t + 1); first by auto => />; inline; islossless => /#. 
wp.
while (true) (16 - t).
  + auto => /> /#.  
auto => /> &hr *; split; [smt() | do (move => *; split)]; 2..5:smt(@W64).
smt(). 
qed.

lemma last_blocks96_ll : islossless M(Syscall).__lastblocks_ref_96.
proof.
proc.
admit.
qed.

lemma blocks0_ref_96_ll : islossless M(Syscall)._blocks_0_ref_96.
proof.
proc.
wp; sp.
if; last by skip. 
while (63 <= to_uint inlen <= 96) (63 - to_uint inlen); last first. 
  + admit.
auto => />. 
inline M(Syscall).__store_H_ref; wp.
while (0 <= to_uint tr <= 64) (64 - to_uint tr).
  + auto => />. inline. islossless. move => &hr * //=. do split; [smt(@W64) | |]. admit. admit. 
inline M(Syscall).__load_H_ref; wp.
while (true) (64 - t + 1); first by auto => />; inline; islossless => /#. 
wp. 
while (true) (16 - t); first by auto => /> /#. 
auto => /> &hr; do (move => *; do split); [smt() | smt() | smt(@W64 pow2_32) | | smt(@W64 pow2_32) |].
admit.
admit.
qed.


lemma sha256_96_ll : islossless M(Syscall).__sha256_96.
proof.
proc.
call store_ref_array_ll; wp.
call blocks1_ref_ll; wp.
call last_blocks96_ll; wp.
call blocks0_ref_96_ll.
inline M(Syscall).__initH_ref; wp.
skip => />.
admit.
qed.

lemma sha256_128_ll : islossless M(Syscall).__sha256_128.
proof.
proc.
call store_ref_array_ll; wp.
call blocks1_ref_ll; wp.
admit.
qed.

lemma sha256_in_ptr_ll : islossless M(Syscall).__sha256_in_ptr.
proof.
proc.
call store_ref_array_ll; wp.
call blocks1_ref_ll; wp.
admit.
qed.

(*** ***)

lemma core_hash_96_ll : islossless M(Syscall).__core_hash__96.
proof.
proc.
inline M(Syscall)._core_hash_96 M(Syscall).__core_hash_96.
wp; sp.
call sha256_96_ll.
skip => />.
qed.

lemma core_hash_128_ll : islossless M(Syscall).__core_hash_128 by proc ; call sha256_128_ll.

lemma core_hash_ptr_ll : islossless M(Syscall).__core_hash_in_ptr by proc ; call sha256_in_ptr_ll.

(*****************************************************************************************************)
(*** PRF, PRF KG, THASH & HASHMSG ***)
(*****************************************************************************************************)

lemma prf_ll : islossless M(Syscall).__prf.
proof.
proc.
call core_hash_96_ll; wp.
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
    call ull_to_bytes_32_ll. auto => /> *. 
    call addr_to_bytes_ll. skip => /> *; rewrite ultE => /#.
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

(*****************************************************************************************************)
(*** WOTS ***)
(*****************************************************************************************************)

lemma base_w_3_2_ll : islossless M(Syscall).__base_w_3_2.
proof.
proc; wp.
while (0 <= consumed <= 3) (3 - consumed); auto => /> /#.
qed.

lemma base_w_64_32_ll : islossless M(Syscall).__base_w_64_32.
proof.
proc; wp.
while (0 <= consumed <= 64) (64 - consumed); auto => /> /#.
qed.

lemma csum_ll : islossless M(Syscall).__csum.
proof.
proc.
while (0 <= to_uint i <= 64) (64 - to_uint i); auto => />; smt(@W64 pow2_64).
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
call base_w_64_32_ll ; wp.
skip => /> *.
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

(*** TODO: Remove this ***)
axiom chain_lengths_post : phoare [M(Syscall).__chain_lengths : true ==> 
  forall (k : int), 0 <= k < 67 => (0 <= (to_uint res.[k]) <= 16) ] = 1%r.    

lemma wots_sign_ll : islossless M(Syscall).__wots_sign.
proof.
proc.
sp ; wp.
while (true) (67 - i).
- auto => />. inline M(Syscall).__set_chain_addr M(Syscall).__gen_chain_inplace_ M(Syscall)._gen_chain_inplace.
  wp; call gen_chain_inplace_ll; auto => /> &hr *. 
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

(*****************************************************************************************************)
(*** XMSS ***)
(*****************************************************************************************************)

lemma ltree_ll : islossless M(Syscall).__l_tree.
proof.
proc.
inline M(Syscall).__set_tree_height.
wp ; sp ; call _x_memcpy_u8u8_32_32_ll; wp.
while (1 <= to_uint l <= 67) (to_uint l - 1); last by skip => />; smt(@W64).
auto; sp.
admit.
qed.


lemma treehash_ll : islossless M(Syscall).__treehash.
proof.
proc.
inline M(Syscall).__copy_subtree_addr M(Syscall).__set_type M(Syscall).__set_ltree_addr M(Syscall).__set_ots_addr.
wp ; sp. 
while (0 <= to_uint idx <= 1 `<<` 10) ((1 `<<` 10) - (to_uint idx)); last first.
  + wp; do 3! call zero_addr_ll; skip => /> *; smt(@W32 pow2_32).
auto => />.
while (0 <= j <= 32) (32 - j).  (* this invariant is wrong *)
  + admit.
inline M(Syscall).__cond_u64_geq_u64_u32_eq_u32.
wp; sp.
seq 11 : (true);2,4,5: admit.
  + wp. admit.
if. 
  + call nbytes_copy_320_352_ll. auto => />. admit.
  + skip => /> &hr *. admit.  (* true is wrong in seq *)
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
inline M(Syscall).__treehash_ M(Syscall)._treehash.
wp ; call treehash_ll.
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
while (0 <= to_uint (loadW64 Glob.mem (to_uint mlen_ptr)) < W64.max_uint /\ 0 <= to_uint i <= 1) (1 - to_uint i); auto => />.
  + inline M(Syscall).__compute_root_ M(Syscall)._compute_root ; wp ; call compute_root_ll ; wp.
    inline M(Syscall).__l_tree_ M(Syscall)._l_tree ; wp ; call ltree_ll ; wp.
    inline M(Syscall).__wots_pk_from_sig_ ; wp ; call wots_pk_from_sig_ll ; wp. skip => /> *. smt(@W32 pow2_32).
  + progress ; smt(@W32). 
  + call hash_msg_ll. inline M(Syscall)._x_memcpy_u8u8p M(Syscall)._memcpy_u8u8p ; wp.
    call memcpy_ptr_ll ; wp. inline M(Syscall)._x__memcpy_u8pu8p M (Syscall)._memcpy_u8pu8p ; wp. 
    call memcpy_ptr_ptr_ll ; wp. call bytes_to_ull_ptr_ll ; wp. do 3! call zero_addr_ll. 
    skip => /> &hr ?? mem. do split; [| | move => *; rewrite ultE]; 1,3:smt(@W64 pow2_64 @JMemory). 
    move => ?. admit.
(* smt(@JMemory @IntDiv @W64 pow2_64). *)
qed.

lemma core_sign_ll : islossless M(Syscall).__xmssmt_core_sign.
proof.
proc.
wp ; sp.
auto => />.
inline M(Syscall).__set_type. 
admit.
qed.

lemma sign_ll : islossless M(Syscall).__xmss_sign by proc; wp; by call core_sign_ll.

(*****************************************************************************************************)
(*** EXPORTED FUNCTIONS ***)
(*****************************************************************************************************)

lemma kg_jazz_ll : islossless M(Syscall).xmss_keypair_jazz.
proof.
proc.
inline M(Syscall).__xmss_keypair M(Syscall).__xmssmt_core_keypair_ M(Syscall)._xmssmt_core_keypair.
wp ; sp. call keypair_ll. by skip.
qed.

lemma sign_jazz_ll : islossless M(Syscall).xmss_sign_jazz by proc; call sign_ll.

lemma sign_open_jazz_ll : 
    phoare [
      M(Syscall).xmss_sign_open_jazz :
      0 <= to_uint (loadW64 Glob.mem (to_uint mlen_ptr)) < W64.max_uint
      ==>
      true
    ] = 1%r.
proof.
proc.
inline M(Syscall).__xmss_sign_open M(Syscall).__xmssmt_core_sign_open_ M(Syscall)._xmssmt_core_sign_open.
wp; sp.
call sign_open_ll.
skip => />.
qed.
