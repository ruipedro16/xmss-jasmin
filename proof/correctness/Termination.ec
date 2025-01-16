pragma Goals : printall.

require import AllCore List RealExp IntDiv.
require import XMSS_IMPL Parameters.

from Jasmin require import JModel.

require import Array67.

(*****************************************************************************************************)
(*** ADDRESS ***)
(*****************************************************************************************************)

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

lemma memset_4_ll : islossless M(Syscall).__memset_u8_3.
proof.
proc.
while (0 <= to_uint i <= 3) (3 - to_uint i); auto => /> *; smt(@W64 pow2_64).
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

lemma gen_chain_inplace_ll : 
    phoare[
        M(Syscall).__gen_chain_inplace : 
        0 <= to_uint start /\
        0 <= to_uint steps <= XMSS_WOTS_W /\
        0 <= to_uint (start + steps) <= XMSS_WOTS_W
        ==> 
        true
      ] = 1%r.
proof.
proc. 
auto => />. 
while (
  #pre /\ 
  to_uint start <= to_uint i <= to_uint (start + steps)
) ((to_uint t) - (to_uint i)); last first. 
    + auto => /> &hr. 
      rewrite /XMSS_WOTS_W => H0 H1 H2 H3 H4; split; [| smt(@W32)]. 
      admit.
auto => />.
inline M(Syscall).__set_hash_addr M(Syscall).__set_key_and_mask 
       M(Syscall).__thash_f_ M(Syscall)._thash_f.
wp; call thash_f_ll.  
auto => /> &hr H0 H1 H2 H3 H4 H5 H6 H7 ; do split; [smt(@W32 pow2_32) | | smt(@W32)].
move => H8. 
rewrite to_uintD_small; first by smt(@W32). 
have ->: to_uint W32.one = 1 by smt(). 
rewrite /XMSS_WOTS_W in H2.
rewrite /XMSS_WOTS_W in H4.
rewrite to_uintD_small; first by smt(@W32).
admit. (* O invariante tem que estar mal *)
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
  + admit.
  + admit.
  + admit.
  + admit.
(*
- inline M(Syscall).__expand_seed_ M(Syscall)._expand_seed ;  wp ; call expand_seed_ll.
  inline M(Syscall).__chain_lengths_ M(Syscall)._chain_lengths ; wp ; call chain_lengths_ll.
  auto => /> /#.
*)
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
admit.
qed.

lemma keypair_seed_ll : islossless M(Syscall).__xmssmt_core_seed_keypair.
proof.
proc.
call nbytes_copy_132_32_ll.
call nbytes_copy_64_32_ll.
inline M(Syscall).__treehash_ M(Syscall)._treehash; wp; call treehash_ll; wp.
call _x_memcpy_u8u8_32_32_ll; wp.
call _x_memcpy_u8u8_32_32_ll; wp.
call _x_memcpy_u8u8_64_64_ll; wp.
inline M(Syscall).__set_layer_addr.
call memset_zero_ll; wp.
call zero_addr_ll.
by auto.
qed.

lemma randombytes_ll : islossless Syscall.randombytes_96 by proc ; islossless; smt(@W8 @Distr @DList).

lemma keypair_ll : islossless M(Syscall).__xmssmt_core_keypair.
proof.
proc.
call keypair_seed_ll ; call randombytes_ll.
by auto.
qed.
