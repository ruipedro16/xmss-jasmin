pragma Goals : printall.

(* Hop 1: The Jasmin program is equivalent to the Jasmin program replacing the prf 
          implementation with a prf operator *)

require import AllCore.

require import XMSS_IMPL XMSS_IMPL_HOP1.

from Jasmin require import JModel.

require import Array32 Array64.

(*** AXIOMS ***)

axiom prf_keygen_hop1 (out : W8.t Array32.t, _in : W8.t Array64.t, key : W8.t Array32.t) :
hoare[M(Syscall).__prf_keygen_ : arg=(out, _in, key) ==> to_list res = _PRF_KEYGEN_ (to_list _in) (to_list key)].

axiom prf_hop1 (out : W8.t Array32.t, _in : W8.t Array32.t, key : W8.t Array32.t):
hoare[M(Syscall).__prf_ : arg=(out, _in, key) ==> res = _PRF_ out _in key].

(*** STDLIB ***)

lemma _x_memcpy_u8u8_32_32_hop1 :
    equiv [M(Syscall)._x_memcpy_u8u8_32_32 ~ Mp(SCall)._x_memcpy_u8u8_32_32 :
      ={arg} ==> ={res}].
proof. proc ; inline ; sim. qed.

lemma _x_memcpy_u8u8_64_64_hop1 :
    equiv [M(Syscall)._x_memcpy_u8u8_64_64 ~ Mp(SCall)._x_memcpy_u8u8_64_64 :
      ={arg} ==> ={res}].
proof. proc ; inline ; sim. qed.


lemma _x_memcpy_u8u8_64_32_hop1 :
    equiv [M(Syscall)._x_memcpy_u8u8_64_32 ~ Mp(SCall)._x_memcpy_u8u8_64_32 :
      ={arg} ==> ={res}].
proof. proc ; inline ; sim. qed.

lemma _x_memcpy_u8pu8_4_hop1 :
    equiv [M(Syscall)._x_memcpy_u8pu8_4 ~ Mp(SCall)._x_memcpy_u8pu8_4 :
      ={arg,Glob.mem} ==> ={res}].
proof. proc; inline*; sim. qed.

lemma _x_memcpy_u8pu8_32_hop1 :
    equiv [M(Syscall)._x_memcpy_u8pu8_32 ~ Mp(SCall)._x_memcpy_u8pu8_32 :
      ={arg,Glob.mem} ==> ={res}].
proof. proc; inline*; sim. qed.


lemma _x_memcpy_u8u8p_hop1 :
    equiv [M(Syscall)._x_memcpy_u8u8p ~ Mp(SCall)._x_memcpy_u8u8p : 
      ={arg,Glob.mem} ==> ={res}].
proof. proc; inline*; sim => />. qed.

lemma ull_to_bytes_32_hop1 :
    equiv [M(Syscall).__ull_to_bytes_32 ~ Mp(SCall).__ull_to_bytes_32 :
      ={arg} ==> ={res}].
proof.
proc ; sim => />.
qed.

lemma addr_to_bytes_hop1 :
    equiv [M(Syscall).__addr_to_bytes ~ Mp(SCall).__addr_to_bytes : ={arg} ==> ={res}].  
proof. proc ; sim => />. qed.

(*** HASH ***)

lemma thash_f_hop1 : 
    equiv [M(Syscall).__thash_f ~ Mp(SCall).__thash_f : ={arg} ==> ={res}].
proof.
proc.
sp.
seq 1 1 : (#pre /\ ={aux}); 1:call ull_to_bytes_32_hop1;auto.
seq 1 1 : (
   addr_as_bytes{2} = witness /\
   bitmask{2} = witness /\
   addr_as_bytes{1} = witness /\
   bitmask{1} = witness /\ 
   ={out, pub_seed, addr, aux, buf}
); 1: auto.
seq 1 1 : (#pre /\ ={addr}); 1:inline;auto.
seq 1 1 : (
   bitmask{2} = witness /\
   bitmask{1} = witness /\ 
   ={out, pub_seed, addr, aux, buf, addr, addr_as_bytes}
); 1:call addr_to_bytes_hop1;auto.
seq 1 1 : (#pre /\ ={aux}). admit. (* error: Cannot infer all placedholders when call prf_hop1 *)
seq 1 1 : (#pre /\ ={buf}); 1:auto.
seq 1 1 : (#pre); 1:inline;auto.
seq 1 1 : (#pre); 1:call addr_to_bytes_hop1;auto.
seq 1 1 : (
  ={out, pub_seed, addr, aux, buf, addr, addr_as_bytes, bitmask}
); 1: admit. (* ecall {1} (prf_hop1 bitmask{1} addr_as_bytes{1} pub_seed{1}). *)
admit.
qed.

lemma _thash_f_hop1 : 
    equiv [M(Syscall).__thash_f_ ~ Mp(SCall).__thash_f_ : ={arg} ==> ={res}].
proof.
proc.
inline M(Syscall)._thash_f Mp(SCall)._thash_f.
wp ; sp.
call thash_f_hop1 ; auto.
qed.

lemma _thash_h_hop1 : 
    equiv [M(Syscall).__thash_h ~ Mp(SCall).__thash_h : ={arg} ==> ={res}].
proof.
proc.
sp.
seq 1 1 : (={out, in_0, pub_seed, addr, buf, aux, addr_as_bytes, bitmask}); 1:call ull_to_bytes_32_hop1;auto.
seq 2 2 : (#pre); 1:inline*;auto.
seq 1 1 : (#pre); 1:call addr_to_bytes_hop1;auto.
seq 1 1 : (#pre). admit. (* call prf_hop1. *)
seq 2 2 : (#pre); 1:inline*;auto.
seq 1 1 : (#pre); 1:call addr_to_bytes_hop1;auto.
seq 1 1 : (#pre).
  + admit. (* call to prf_hop1 *)
seq 1 1 : (#pre /\ ={bitmask}); 1:auto.
seq 1 1 : (#pre); 1:inline*;auto.
seq 1 1 : (#pre); 1:call addr_to_bytes_hop1;auto.
seq 1 1 : (#pre); 1:admit. (* TODO: Call to  prf_hop_1 *)
seq 1 1 : (#pre); 1:auto.
sp.
seq 1 1 : (={out,buf}); last by admit. (* isto isola o while. depois preciso de uma pos condicao decente para conseguir provar #post em vez de true *)
while (
   ={out, in_0, pub_seed, addr, buf, aux, addr_as_bytes, bitmask, i} /\
   0 <= to_uint i{1} <= 2 * 32 /\
   0 <= to_uint i{2} <= 2 * 32
); last by skip => />.
seq 2 2 : (#pre /\ ={t}); 1:auto.
seq 2 2 : (#pre /\ ={buf, i}).
auto => /> *; do split; 1..4:smt(@W64). admit. admit. (*OVERFLOW*)
skip => />. 
qed.

lemma hash_message_hop1 : 
    equiv[M(Syscall).__hash_message ~ Mp(SCall).__hash_message :
        ={arg, Glob.mem} ==> ={res}].
proof.
proc.
seq 2 2 : (={Glob.mem, mhash, r, root, idx, m_with_prefix_ptr, mlen, buf, buf_n}); 1:auto.
seq 2 2 : (#pre /\ ={offset}); 1:inline*;sim => />.
seq 10 10 : (#pre); 1:inline*;sim => />.
admit.
qed.

(*** WOTS ***)

lemma expand_seed_hop1 : 
    equiv [M(Syscall).__expand_seed ~ Mp(SCall).__expand_seed : ={arg} ==> ={res}].
proof.
proc.
seq 2 2 : (#pre /\ ={buf, ith_seed}); 1:auto.
seq 2 2 : (#pre /\ ={addr}); 1:inline;auto.
seq 1 1 : (#pre /\ ={aux}); 1:call (_x_memcpy_u8u8_32_32_hop1);auto.
seq 2 2 : (#pre /\ ={buf, i}); 1:auto.
while (
  0 <= i{1} <= 67 /\ ={i, ith_seed, addr, outseeds, buf} /\
  aux_list{2} = to_list aux{1}
); last first.
    + skip => /> &2 ; do split; 1,2,3: admit.
    + seq 1 1 : (#pre); 1:inline*;auto.
      seq 1 1 : (#pre /\ ={aux}).
       * call addr_to_bytes_hop1. skip => /> &1 &2 *. admit.
      admit.
qed.

lemma base_w_3_2_hop1 :
    equiv[M(Syscall).__base_w_3_2 ~ Mp(SCall).__base_w_3_2 : ={arg}  ==> ={res}].
proof. proc ; sim => />. qed.

lemma base_w_67_32_hop1 :
    equiv[M(Syscall).__base_w_67_32 ~ Mp(SCall).__base_w_67_32 : ={arg}  ==> ={res}].
proof. proc ; sim => />. qed.

lemma csum_hop1 :
    equiv[M(Syscall).__csum ~ Mp(SCall).__csum : ={arg} ==> ={res}].
proof. proc ; sim => />. qed. 

lemma checksum_hop1 :
    equiv[M(Syscall).__wots_checksum ~ Mp(SCall).__wots_checksum : ={arg} ==> ={res}].
proof.
proc.
sim => />.
qed.

lemma chain_lengths_hop1 :
    equiv [M(Syscall).__chain_lengths ~ Mp(SCall).__chain_lengths : ={arg} ==> ={res}].
proof.
proc.
seq 1 1 : (#pre /\ ={t}); 1:auto.
seq 1 1 : (#pre /\ ={lengths}); 1:call base_w_67_32_hop1;auto.
seq 1 1 : (#pre); 1:auto.
seq 1 1 : (#pre); 1:call checksum_hop1;auto.
qed.

lemma gen_chain_hop1 :
    equiv [M(Syscall).__gen_chain ~ Mp(SCall).__gen_chain : ={arg,Glob.mem} ==> ={res}].
proof.
proc.
seq 1 1 : (={out, in_ptr, start, steps, pub_seed, addr}); 1:call _x_memcpy_u8u8p_hop1;auto.
seq 3 3 : (#pre /\ ={t}); 1:auto.
admit.
qed.

lemma gen_chain_inplace_hop1 :
    equiv [M(Syscall).__gen_chain_inplace ~ Mp(SCall).__gen_chain_inplace :
      ={arg} ==> ={res}].
proof.
proc.
sp.
while (={i,out,pub_seed,addr,steps}); last by skip => />.
seq 1 1 : (#pre); 1:inline;auto.
call _thash_f_hop1;auto => />. 
qed.

lemma _gen_chain_inplace_hop1 :
    equiv [M(Syscall).__gen_chain_inplace_ ~ Mp(SCall).__gen_chain_inplace_ :
      ={arg} ==> ={res}].
proof.
proc.
inline M(Syscall)._gen_chain_inplace Mp(SCall)._gen_chain_inplace.
sp; wp.
call gen_chain_inplace_hop1 ; auto.
qed.

lemma wots_pkgen_hop1 :
    equiv [M(Syscall).__wots_pkgen ~ Mp(SCall).__wots_pkgen : ={arg} ==> ={res}].
proof.
proc.
seq 1 1 : (#pre /\ ={pk, addr}).
  + inline M(Syscall).__expand_seed_ M(Syscall)._expand_seed Mp(SCall).__expand_seed_  Mp(SCall)._expand_seed. wp ; sp. call expand_seed_hop1. auto.
sp. 
while (={i,pk,pub_seed,addr} /\ 0 <= i{1} <= 67); last by auto.
seq 1 1 : (#pre /\ ={chain}); 1:auto.
seq 1 1 : (#pre); 1:inline;auto.
call _gen_chain_inplace_hop1.
auto => /> /#.
qed.

lemma wots_sign_hop1 :
    equiv [M(Syscall).__wots_sign ~ Mp(SCall).__wots_sign : ={arg} ==> ={res}].
proof.
proc.
sp.
seq 1 1 : (={sig, msg, seed, pub_seed, addr, lengths}).
  + inline M(Syscall).__chain_lengths_ M(Syscall)._chain_lengths 
           Mp(SCall).__chain_lengths_ Mp(SCall)._chain_lengths; wp ; sp.
    call chain_lengths_hop1. auto.
seq 1 1 : (#pre). 
  + inline M(Syscall).__expand_seed_ M(Syscall)._expand_seed
           Mp(SCall).__expand_seed_ Mp(SCall)._expand_seed; wp ; sp.
    call expand_seed_hop1. auto.
sp.
while (={sig, msg, seed, pub_seed, addr, lengths, i} /\ 0 <= i{1} <= 67); last by skip => />.
seq 1 1 : (#pre /\ ={chain}); 1:auto.
seq 1 1 : (#pre /\ ={addr}); 1:inline;auto.
seq 1 1 : (#pre /\ ={aux_0, aux_1}); 1:call gen_chain_inplace_hop1;auto.
(* TODO: call the gen_chain locla function in the code (not the inline) *)
auto => /> /#.
qed.

lemma wots_pk_from_sig_hop1 :
    equiv [M(Syscall).__wots_pk_from_sig ~ Mp(SCall).__wots_pk_from_sig : 
      ={arg,Glob.mem} ==> ={res}].
proof.
proc.
sp.
seq 1 1 : (={pk, sig_ptr, msg, pub_seed, addr, lengths, Glob.mem}).
  + inline M(Syscall).__chain_lengths_ M(Syscall)._chain_lengths
           Mp(SCall).__chain_lengths_ Mp(SCall)._chain_lengths; wp ; sp.
    call chain_lengths_hop1. auto.
sp.
while (={pk, sig_ptr, msg, pub_seed, addr, lengths, i, Glob.mem} /\ 0 <= i{1} <= 67); last by skip => />.
seq 1 1 : (#pre /\ ={chain}); 1:auto.
seq 1 1 : (#pre /\ ={addr}); 1:inline*;auto.
seq 3 3 : (#pre /\ ={start,steps}); 1:auto.
seq 2 2 : (#pre /\ ={t}); 1:auto.
seq 1 1 : (#pre /\ ={aux_0, aux_1}).
  + inline M(Syscall).__gen_chain_ M(Syscall)._gen_chain
           Mp(SCall).__gen_chain_ Mp(SCall)._gen_chain ; wp ; sp.
    call gen_chain_hop1. skip => />. 
skip => /> /#.
qed.

(*** XMSS COMMONS ***)

lemma ltree_hop1 :
    equiv [M(Syscall).__l_tree ~ Mp(SCall).__l_tree :
      ={arg,Glob.mem} ==> ={res}].
proof.
proc.
sp.
seq 1 1 : (#pre /\ ={addr}); 1:inline;auto.
admit.
qed.

lemma compute_root_hop1 :
  equiv [M(Syscall).__compute_root ~ Mp(SCall).__compute_root :
      ={arg,Glob.mem} ==> ={res}].
proof.
proc.
sp.
if; first by auto.
  + admit.
  + admit.
qed.

lemma gen_leaf_wots_hop1 :
    equiv[M(Syscall).__gen_leaf_wots ~ Mp(SCall).__gen_leaf_wots :
      ={arg,Glob.mem} ==> ={res}].
proof.
proc.
seq 2 2 : (={Glob.mem, leaf, sk_seed, pub_seed, ltree_addr, ots_addr, pk, _0}); 1:auto.
seq 1 1 : (#pre /\ ={pk}); 1:call wots_pkgen_hop1;auto. 
seq 1 1 : (#pre).
  + inline M(Syscall).__l_tree_ M(Syscall)._l_tree
           Mp(SCall).__l_tree_ Mp(SCall)._l_tree. wp ; sp.
    call ltree_hop1;auto.
auto.
qed.

lemma set_result_hop1 : 
    equiv [M(Syscall).__set_result ~ Mp(SCall).__set_result :
      ={arg,Glob.mem} ==> ={res}].
proof. proc ; sim => />. qed.

lemma xmssmt_core_sign_open :
    equiv [M(Syscall).__xmssmt_core_sign_open ~ Mp(SCall).__xmssmt_core_sign_open :
      ={arg,Glob.mem} ==> ={res}].
proof.
proc.
seq 13 13 : (={buf, leaf, ltree_addr, node_addr, root, wots_pk, sm_offset, pub_root,
         pub_seed, idx, Glob.mem, smlen, mlen_ptr, buf, sm_ptr, m_ptr, pk}); 1:auto.
seq 6 6 : (#pre); 1:inline* ; sim => />.
seq 3 3 : (#pre /\ ={t64}); 1:auto.
seq 7 7 : (#pre /\ ={offset_out, offset_in, bytes}); 1:inline*;sim => />.
seq 1 1 : (#pre); 1:call _x_memcpy_u8u8p_hop1;auto.
seq 4 4 : (#pre /\ ={idx_hash}); 1:auto.
seq 1 1 : (#pre).
  + call hash_message_hop1. skip => /> *. admit.
seq 3 3 : (#pre /\ ={sm_offset, i}); 1:auto.
admit.
qed.

(*** XMSS CORE ***)

(* TODO: Remove the _array suffix *)
lemma treehash_array_hop1 :
    equiv[M(Syscall).__treehash_array ~ Mp(SCall).__treehash_array : 
        ={Glob.mem, arg} ==> ={res}].
proof.
proc.
seq 18 18 : (={Glob.mem, root, auth_path, sk_seed, pub_seed, leaf_idx, subtree_addr,
             _stack, buf, buf2, heights, ltree_addr, node_addr, ots_addr, offset, idx}).
  + inline*; sim.
while (
  #pre /\ ={j} /\
  0 <= to_uint idx{1} <= (1 `<<` 10)
); first by auto.
admit.
qed.

lemma xmssmt_core_seed_keypair_hop1 :
    equiv[M(Syscall).__xmssmt_core_seed_keypair ~ Mp(SCall).__xmssmt_core_seed_keypair :
      ={Glob.mem, arg} ==> ={res}].
proof.
proc.
seq 7 7 : (={Glob.mem, pk, sk, seed, _0, auth_path, buf, top_tree_addr, aux}).
  + inline* ; sim.
seq 1 1 : (#pre); 1:auto.
seq 1 1 : (#pre /\ ={aux_0}); 1:inline*; sim.
seq 1 1 : (#pre); 1:auto.
seq 1 1 : (#pre /\ ={aux_1}); 1:inline*;sim.
seq 1 1 : (#pre); 1:auto.
seq 2 2 : (#pre /\ ={aux_1}); 1:inline*;sim.
inline M(Syscall).__treehash_array_ M(Syscall)._treehash_array
       Mp(SCall).__treehash_array_ Mp(SCall)._treehash_array.
wp ; sp.
call treehash_array_hop1.
skip => />.
qed.

lemma xmssmt_core_keypair_hop1 :
    equiv[M(Syscall).__xmssmt_core_keypair ~ Mp(SCall).__xmssmt_core_keypair :
      ={arg,Glob.mem} ==> ={res}].
proof.
proc.
seq 3 3 : (={pk, sk, Glob.mem, seed, seed_p}); 1:auto.
seq 1 1 : (#pre); 1:sim.
call xmssmt_core_seed_keypair_hop1.
skip => />.
qed.

lemma xmssmt_core_sign_hop1 :
    equiv [M(Syscall).__xmssmt_core_sign ~ Mp(SCall).__xmssmt_core_sign :
      ={Glob.mem, arg} ==> ={res}].
proof.
proc.
seq 10 10 : (={Glob.mem, sk, sm_ptr, smlen_ptr, m_ptr, mlen, auth_path, buf, idx_bytes,
               ots_addr, pub_root, pub_seed, root, sig, sk_prf, sk_seed}); 1:sim.
seq 3 3 : (#pre); 1:inline*;sim.
seq 4 4 : (#pre /\ ={idx}); 1:sim.
if; first by auto.
  + admit.
  + admit.
qed.

(*** XMSS ***)

lemma xmss_keypair_hop1 :
    equiv[M(Syscall).__xmss_keypair ~ Mp(SCall).__xmss_keypair :
      ={arg,Glob.mem} ==> ={res}].
proof.
proc.
seq 4 4 : (={Glob.mem, pk, sk, oid}); 1:auto.
seq 1 1 : (#pre /\ ={aux, aux_0}).
  + inline M(Syscall).__xmssmt_core_keypair_ M(Syscall)._xmssmt_core_keypair
           Mp(SCall).__xmssmt_core_keypair_ Mp(SCall)._xmssmt_core_keypair.
    wp ; sp. call xmssmt_core_keypair_hop1. skip => />.
sim.
qed.

lemma xmss_sign_hop1 :
    equiv[M(Syscall).__xmss_sign ~ Mp(SCall).__xmss_sign :
      ={arg, Glob.mem} ==> ={res}].
proof.
proc.
seq 1 1 : (={sk, sm_ptr, smlen_ptr, m_ptr, mlen, Glob.mem, aux, aux_0}).
  + wp ; sp. call xmssmt_core_sign_hop1. auto => />. admit. (* memL = memR ??? *)
sim.
qed.
