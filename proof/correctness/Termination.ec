pragma Goals : printall.

require import AllCore List RealExp IntDiv.
require import XMSS_IMPL XMSS_IMPL_PP Generic Parameters.

from Jasmin require import JModel.

lemma bytes_to_ull_ptr_ll : islossless Mp(Syscall).__bytes_to_ull_ptr.
proof.
proc.
while (0 <= to_uint i <= 4) (4 - to_uint i) ; auto => /> * ; last by smt(@W64).
do split.
  + rewrite to_uintD /#.
  + smt(@W64).
  + rewrite to_uintD ; smt(@W64).
qed.

lemma bytes_to_ull_ll : islossless Mp(Syscall).__bytes_to_ull.
proof.
proc.
while (0 <= to_uint i <= 4) (4 - to_uint i); auto => /> *; last by smt(@W64).
do split.
  + rewrite to_uintD /#.
  + smt(@W64).
  + rewrite to_uintD ; smt(@W64).
qed.

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

lemma memcpy_ptr_32_ll : islossless Mp(Syscall).__memcpy_u8u8p_32.
proof.
proc.
while (0 <= to_uint i <= 32) (32 - to_uint i) ; auto => /> *.
- do split ; 1,3: by rewrite to_uintD_small /#. smt(@W64).
- smt(@W64).
qed.

lemma memcpy_32_ptr_ll : islossless Mp(Syscall).__memcpy_u8pu8_32.
proof.
proc.
while (0 <= to_uint i <= 32) (32 - to_uint i) ; auto => /> *.
- do split.
  + rewrite to_uintD_small /#.
  + smt(@W64).
  + rewrite to_uintD ; smt(@W64).
- smt(@W64).
qed.

lemma memcpy_ptr_ptr_ll : islossless Mp(Syscall).__memcpy_u8pu8p.
proof.
proc.
while (0 <= to_uint i <= to_uint bytes) ((to_uint bytes) - (to_uint i)) ; auto => /> *.
- do split.
  + rewrite to_uintD ; smt(@W64).
  + smt(@W64).
  + smt(@W64).
- smt(@W64).
qed.

lemma memset_zero_ll : islossless Mp(Syscall).__memset_zero_u8.
proof.
proc.
while (0 <= to_uint i <= 4) (4 - to_uint i) ; auto => /> *.
do split.
  + rewrite to_uintD_small /#.
  + smt(@W64).
  + rewrite to_uintD_small ; smt(@W64).
- smt(@W64).
qed.

lemma memset_u8_ptr_ll : phoare [Mp(Syscall).__memset_u8_ptr : 0 <= to_uint inlen < W64.modulus ==> true] = 1%r.
proof.
proc.
while (0 <= to_uint i <= to_uint inlen) ((to_uint inlen) - (to_uint i)) ; auto => /> ; progress ; smt(@W64).
qed.

lemma memset_4_ll : islossless Mp(Syscall).__memset_u8_4.
proof.
proc.
while (0 <= to_uint i <= 4) (4 - to_uint i); auto => /> *; last by smt(@W64).
do split ; [rewrite to_uintD /# | smt(@W64) | rewrite to_uintD ; smt(@W64)].
qed.

lemma memset_128_ll : islossless Mp(Syscall).__memset_u8_128.
proof.
proc.
while (0 <= to_uint i <= 128) (128 - to_uint i); auto => /> *; last by smt(@W64).
do split ; [rewrite to_uintD /# | smt(@W64) | rewrite to_uintD ; smt(@W64)].
qed.

lemma memcmp_ll : islossless Mp(Syscall).__memcmp.
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

lemma thash_f_ll : islossless Mp(Syscall).__thash_f.
proof.
proc.
auto => />.
while (0 <= to_uint i <= 32) (32 - to_uint i) ; auto => />.
  - auto => /> *. do split ; 1,2: by smt(@W64). rewrite to_uintD_small => /#.
  - auto => /> *. split ; [ progress ; rewrite ultE => /# | auto ].
  - call addr_to_bytes_ll. inline Mp(Syscall).__set_key_and_mask ; auto => />. 
    call addr_to_bytes_ll ; auto => />. 
    call ull_to_bytes_32_ll. auto => /> *. rewrite ultE => /#.
qed.

lemma thash_h_ll : islossless Mp(Syscall).__thash_h.
proof.
proc.
inline  Mp(Syscall).__set_key_and_mask ; wp.
while (0 <= to_uint i <= 2 * 32) ((2*32) - (to_uint i)).
- auto => />. progress.
  + rewrite to_uintD_small /#.
  + smt(@W64).
  + rewrite to_uintD_small ; [smt() | smt(@W64)].
- wp. do (call addr_to_bytes_ll ; wp). call ull_to_bytes_32_ll. auto => /> *. smt(@W64).
qed.

lemma hash_msg_ll : islossless Mp(Syscall).__hash_message.
proof.
proc.
inline Mp(Syscall)._x_memcpy_u8pu8_32 Mp(Syscall)._memcpy_u8pu8_32 ; wp.
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

lemma csum_ll : islossless Mp(Syscall).__csum.
proof.
proc.
while (0 <= to_uint i <= 64) (64 - to_uint i); auto => />.
  - move => ?. rewrite ultE of_uintK /= => *. rewrite to_uintD_small => /#.
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
- inline Mp(Syscall)._x_memcpy_u8u8p_32 Mp(Syscall)._memcpy_u8u8p_32. wp.
  call memcpy_ptr_32_ll. auto => />. progress ; [ rewrite to_uintD_small /# | smt(@W64) ].
qed.

lemma chain_lengths_ll : islossless Mp(Syscall).__chain_lengths.
proof.
proc ; wp.
call checksum_ll ; wp.
call base_w_ll ; wp.
skip => /> *.
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

lemma wots_sign_ll : islossless Mp(Syscall).__wots_sign.
proof.
proc.
sp ; wp.
while (true) (67 - i).
- auto => />. inline Mp(Syscall).__set_chain_addr ; call gen_chain_inplace_ll ; auto => /> *. 
  rewrite /XMSS_WOTS_W ; do split.
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
  call gen_chain_ll. auto => /> *. rewrite /XMSS_WOTS_W //=. do split.
  + smt(@Array67 @W32).
  + admit.
  + smt (@Array67 @W32).
  + admit.
  + smt (@Array67 @W32).
  + admit.
  + progress => /#.
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
- auto => />; first by progress ; 1,3:smt(@W32) ; smt(). do call zero_addr_ll.
  skip => /> * ; do split.
  + admit.
  + admit.
  + move => *. split ; last by smt(). rewrite ultE. move => ???. rewrite of_uintK. admit. (* TODO: no info about idx *)
qed.

lemma gen_leaf_ll : islossless Mp(Syscall).__gen_leaf_wots.
proof.
proc.
inline Mp(Syscall).__l_tree_ Mp(Syscall)._l_tree ; wp ; call ltree_ll.
wp ; call pkgen_ll ; wp. 
by skip.
qed.

lemma compute_root_ll : islossless Mp(Syscall).__compute_root.
proof.
proc.
inline Mp(Syscall).__set_tree_height Mp(Syscall).__set_tree_index.
call thash_h_ll. wp.
while (0 <= to_uint i <= (10 - 1)) ((10 - 1) - (to_uint  i)).
- progress.  wp. inline Mp(Syscall)._x_memcpy_u8u8p_32 Mp(Syscall)._memcpy_u8u8p_32. sp ; if.
  + wp ; call memcpy_ptr_32_ll. wp ; call thash_h_ll. auto => /> *. do split.
    * rewrite to_uintD_small /#.
    * smt(@W64).
    * rewrite to_uintD_small ; smt(@W64).
  + wp ; call memcpy_ptr_32_ll. wp ; call thash_h_ll. auto => /> *. do split.
    * rewrite to_uintD_small /#.
    * smt(@W64).
    * rewrite to_uintD_small ; smt(@W64).
- wp ; sp. if.
  + inline Mp(Syscall)._x_memcpy_u8u8p_32 Mp(Syscall)._memcpy_u8u8p_32 ;wp ; call memcpy_ptr_32_ll.
    wp. call memcpy_ll. skip => />. progress.
     * by rewrite /to_list size_mkseq.
     * smt(@W64).
  + inline Mp(Syscall)._x_memcpy_u8u8p_32 Mp(Syscall)._memcpy_u8u8p_32 ; wp ; call memcpy_ptr_32_ll. 
    wp ; call memcpy_ll. skip => /> *. split.
     * by rewrite /to_list size_mkseq.
     * smt (@W64).
qed.

lemma keypair_seed_ll : islossless Mp(Syscall).__xmssmt_core_seed_keypair.
proof.
proc.
while (0 <= i <= 32) (32 - i) ; first by auto => /> /#.
wp.
while (0 <= i <= 32) (32 - i) ; first by auto => /> /#.
inline Mp(Syscall).__treehash_array_ Mp(Syscall)._treehash_array.
wp ; call treehash_array_ll.
do (wp ; call memcpy_ll).
wp. call memset_zero_ll.
inline Mp(Syscall).__set_layer_addr.
wp ; sp. call zero_addr_ll.
skip ; progress; by smt(@List @Array96 @Array64 @Array32).
qed.

lemma randombytes_ll : islossless Syscall.randombytes_96
    by proc ; islossless ; smt.

lemma keypair_ll : islossless Mp(Syscall).__xmssmt_core_keypair.
proof.
proc.
call keypair_seed_ll ; call randombytes_ll.
by auto.
qed.

lemma set_result_ll : phoare [Mp(Syscall).__set_result :
      0 <= to_uint (loadW64 Glob.mem (to_uint mlen_ptr)) < W64.max_uint ==> true] = 1%r.
proof.
proc.
if.
- wp; call memset_u8_ptr_ll. auto => /> /#.
- inline Mp(Syscall)._x__memcpy_u8pu8p Mp(Syscall)._memcpy_u8pu8p ; wp.
  call memcpy_ptr_ptr_ll. wp ; skip => /> *.
qed.

lemma sign_open_ll : phoare [Mp(Syscall).__xmssmt_core_sign_open :
    0 <= to_uint (loadW64 Glob.mem (to_uint mlen_ptr)) < W64.max_uint ==>
    true] = 1%r.
proof.
proc.
wp ; sp.
inline Mp(Syscall).__set_type Mp(Syscall).__set_layer_addr  Mp(Syscall).__set_tree_addr Mp(Syscall).__set_ots_addr 
       Mp(Syscall).__set_ltree_addr.
sp ; wp.
call set_result_ll. call memcmp_ll.
while (0 <= to_uint i <= 1) (1 - to_uint i); auto => />.
  + inline Mp(Syscall).__compute_root_ Mp(Syscall)._compute_root ; wp ; call compute_root_ll ; wp.
    inline Mp(Syscall).__l_tree_ Mp(Syscall)._l_tree ; wp ; call ltree_ll ; wp.
    inline Mp(Syscall).__wots_pk_from_sig_ ; wp ; call wots_pk_from_sig_ll ; wp. skip => /> * ; do split.
    * rewrite to_uintD_small /#.
    * smt(@W32).
    * smt(@W32).
  + progress ; smt(@W32). 
  + call hash_msg_ll ; inline Mp(Syscall)._x_memcpy_u8u8p_32 Mp(Syscall)._memcpy_u8u8p_32 ; wp.
    call memcpy_ptr_32_ll ; wp. inline Mp(Syscall)._x__memcpy_u8pu8p Mp(Syscall)._memcpy_u8pu8p ; wp. 
    call memcpy_ptr_ptr_ll ; wp. call bytes_to_ull_ptr_ll ; wp. do 3! call zero_addr_ll. 
    skip => /> *. progress.
    * smt(@W32).
    * smt.
    * admit.
qed.

lemma sign_ll : islossless Mp(Syscall).__xmssmt_core_sign.
proof.
proc.
wp ; sp.
admit.
qed.



(******************************* exported functions **********************************)
lemma kg_ll : islossless Mp(Syscall).xmss_keypair_jazz.
proof.
proc.
inline Mp(Syscall).__xmss_keypair Mp(Syscall).__xmssmt_core_keypair_ Mp(Syscall)._xmssmt_core_keypair.
wp ; sp. call keypair_ll. by skip.
qed.
