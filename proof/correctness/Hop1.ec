pragma Goals : printall.

(* Hop 1: The Jasmin program is equivalent to the Jasmin program replacing the prf 
          implementation with a prf operator *)

require import AllCore List.

require import RandomBytes XMSS_IMPL XMSS_IMPL_HOP1.

from Jasmin require import JModel.

require import Array32 Array64 Array67 Array96 Array128 Array2144.

(*** Hash & PRF ***)

lemma hash_96_hop1 (x : W8.t Array96.t) :
    phoare [M(Syscall).__core_hash_96 : 
      arg.`2 = x ==> res = Array32.of_list witness (Hash (to_list x))] = 1%r.
proof.
proc.
admit.
qed.

lemma hash_128_hop1 (x : W8.t Array128.t) :
    phoare [M(Syscall).__core_hash_128 : 
      arg.`2 = x ==> res = Array32.of_list witness (Hash (to_list x))] = 1%r.
proof.
proc.
admit.
qed.

lemma hash_ptr_hop1 (ptr len : W64.t) :
    phoare [M(Syscall).__core_hash_in_ptr :
      arg.`2=ptr /\ arg.`3=len ==> res = Hash_ptr ptr len] = 1%r.
proof.
proc.
admit.
qed.

op prf_padding_bytes : W8.t list = nseq 32 (W8.of_int 3). (* 3 = XMSS_HASH_PADDING_PRF *)
op prf_keygen_padding_bytes : W8.t list = nseq 32 (W8.of_int 4). (* 4 = XMSS_HASH_PADDING_PRF_KEYGEN *)

op encode_prf (in_0  key : W8.t Array32.t) : W8.t Array96.t =
  Array96.of_list witness (prf_padding_bytes ++ to_list in_0 ++ to_list key).

op encode_prf_keygen (in_0 : W8.t Array64.t, key : W8.t Array32.t) : W8.t Array128.t =
  Array128.of_list witness (prf_keygen_padding_bytes ++ to_list in_0 ++ to_list key).

lemma prf_keygen_hop1 (_in: W8.t Array64.t, key : W8.t Array32.t) :
    phoare[M(Syscall).__prf_keygen_ : 
      arg.`2=_in /\ arg.`3=key ==> res = _PRF_KEYGEN_  _in key] = 1%r.
proof.
proc.
inline M(Syscall)._prf_keygen M(Syscall).__prf_keygen.
wp ; sp.
idtac. admit.
qed.

lemma  prf_hop1 (out : W8.t Array32.t, _in : W8.t Array32.t, key : W8.t Array32.t):
    phoare[M(Syscall).__prf_ : arg=(out, _in, key) ==> res = _PRF_ out _in key] = 1%r.
proof.
proc.
inline M(Syscall)._prf M(Syscall).__prf.
wp ; sp.
admit.
qed.

(*** STDLIB ***)

lemma memset_u8_4_hop1 : 
    equiv [M(Syscall).__memset_u8_4 ~ M_Hop1(Syscall).__memset_u8_4 : ={arg} ==> ={res}] by proc; sim.

lemma memset_u8_128_hop1 : 
    equiv [M(Syscall).__memset_u8_128 ~ M_Hop1(Syscall).__memset_u8_128 : ={arg} ==> ={res}] by proc; sim.

lemma memset_u8_ptr_hop1 :
    equiv [M(Syscall).__memset_u8_ptr ~ M_Hop1(Syscall).__memset_u8_ptr : 
      ={arg, Glob.mem} ==> ={res,Glob.mem}] by proc; sim => />.

lemma _x_memcpy_u8u8_32_32_hop1 :
    equiv [M(Syscall)._x_memcpy_u8u8_32_32 ~ M_Hop1(Syscall)._x_memcpy_u8u8_32_32 :
      ={arg} ==> ={res}] by proc ; inline ; sim.

lemma _x_memcpy_u8u8_64_64_hop1 :
    equiv [M(Syscall)._x_memcpy_u8u8_64_64 ~ M_Hop1(Syscall)._x_memcpy_u8u8_64_64 :
      ={arg} ==> ={res}] by proc ; inline ; sim.

lemma _x_memcpy_u8u8_64_32_hop1 :
    equiv [M(Syscall)._x_memcpy_u8u8_64_32 ~ M_Hop1(Syscall)._x_memcpy_u8u8_64_32 :
      ={arg} ==> ={res}] by proc ; inline ; sim.

lemma _x_memcpy_u8pu8_4_hop1 :
    equiv [M(Syscall)._x_memcpy_u8pu8_4 ~ M_Hop1(Syscall)._x_memcpy_u8pu8_4 :
      ={arg,Glob.mem} ==> ={res, Glob.mem}] by proc; inline*; sim.

lemma _x_memcpy_u8pu8_32_hop1 :
    equiv [M(Syscall)._x_memcpy_u8pu8_32 ~ M_Hop1(Syscall)._x_memcpy_u8pu8_32 :
      ={arg,Glob.mem} ==> ={res, Glob.mem}] by proc; inline*; sim.

lemma _x_memcpy_u8u8p_hop1 :
    equiv [M(Syscall)._x_memcpy_u8u8p ~ M_Hop1(Syscall)._x_memcpy_u8u8p : 
      ={arg,Glob.mem} ==> ={res}] by proc; inline*; sim => />. 

lemma memcpy_u8u8_2_1_hop1 :
    equiv [M(Syscall).__memcpy_u8u8_2_32_2144 ~ M_Hop1(Syscall).__memcpy_u8u8_2_32_2144 :
      ={arg} ==> ={res}] by proc; sim => />.

lemma memcpy_u8u8_2_2_hop1 :
    equiv [M(Syscall).__memcpy_u8u8_2_64_2144 ~ M_Hop1(Syscall).__memcpy_u8u8_2_64_2144 :
      ={arg} ==> ={res}] by proc ;sim => />.
  
lemma memcpy_offset_hop1 :
    equiv[M(Syscall).__memcpy_u8u8_offset ~ M_Hop1(Syscall).__memcpy_u8u8_offset :
       ={arg} ==> ={res}].
proof.
proc.
sim => />. 
qed.

lemma ull_to_bytes_32_hop1 :
    equiv [M(Syscall).__ull_to_bytes_32 ~ M_Hop1(Syscall).__ull_to_bytes_32 :
      ={arg} ==> ={res}].
proof.
proc ; sim => />.
qed.

lemma ull_to_bytes_4_hop1 :
    equiv [M(Syscall).__ull_to_bytes_4 ~ M_Hop1(Syscall).__ull_to_bytes_4 :
      ={arg} ==> ={res}].
proof.
proc ; sim => />.
qed.


lemma addr_to_bytes_hop1 :
    equiv [M(Syscall).__addr_to_bytes ~ M_Hop1(Syscall).__addr_to_bytes : ={arg} ==> ={res}].  
proof. proc ; sim => />. qed.

(*** HASH ***)

lemma thash_f_hop1 : 
    equiv [M(Syscall).__thash_f ~ M_Hop1(Syscall).__thash_f : ={arg} ==> ={res}].
proof.
proc.
sp.
seq 1 1 : (#pre /\ ={aux}); 1:call ull_to_bytes_32_hop1;auto.
seq 1 1 : ( (* Same as #pre byt without the buf{1,2} = witness *)
  addr_as_bytes{2} = witness /\
  bitmask{2} = witness /\
  addr_as_bytes{1} = witness /\
  bitmask{1} = witness /\ 
  ={out, pub_seed, addr, aux, buf}
); 1:auto => />. 
seq 1 1 : (#pre); 1:inline*;auto.
seq 1 1 : ( (* Same as #pre but without addr_as_bytes{1,2} = witness *)
  bitmask{2} = witness /\
  bitmask{1} = witness /\ 
  ={out, pub_seed, addr, aux, buf, addr_as_bytes}
); 1:call addr_to_bytes_hop1;auto => />.
seq 1 1 : (#pre). (* we already have ={aux} in #pre *)
    + exists * (init (fun (i_0 : int) => buf{1}.[32 + i_0]))%Array32, addr_as_bytes{1}, pub_seed{1}.
      elim * => _P1 _P2 _P3.
      call {1} (prf_hop1 _P1 _P2 _P3); auto => />.
seq 1 1 : (#pre) (* ={buf} is already in #pre *); 1:auto.
seq 1 1 : (#pre). 
    + inline M(Syscall).__set_key_and_mask M_Hop1(Syscall).__set_key_and_mask; auto.
seq 1 1 : (#pre); 1:call addr_to_bytes_hop1;auto => />.
seq 1 1 : (={out, pub_seed, addr, aux, buf, addr_as_bytes, bitmask}).
    + ecall {1} (prf_hop1 bitmask{1} addr_as_bytes{1} pub_seed{1}). auto => />.
seq 2 2 : (={buf}); last first.
    + inline M(Syscall).__core_hash__96 M(Syscall)._core_hash_96. wp ; sp.
      ecall {1} (hash_96_hop1 in_00{1}). auto => />.
while (
  #pre /\
  0 <= to_uint i{1} <= 32 /\
  ={i}
).
    + auto => /> &2 *; smt(@W64).
    + auto => />.
qed.


lemma _thash_h_hop1 : 
    equiv [M(Syscall).__thash_h ~ M_Hop1(Syscall).__thash_h : ={arg} ==> ={res}].
proof.
proc.
sp.
seq 1 1 : (={out, in_0, pub_seed, addr, buf, aux, addr_as_bytes, bitmask}); 1:call ull_to_bytes_32_hop1;auto.
seq 2 2 : (#pre); 1:inline*;auto.
seq 1 1 : (#pre); 1:call addr_to_bytes_hop1;auto.
seq 1 1 : (#pre). 
  + exists * (init (fun (i_0 : int) => (buf{1}.[32 + i_0])))%Array32, addr_as_bytes{1},  pub_seed{1}.
    elim * => _P1 _P2 _P3. call {1} (prf_hop1 _P1 _P2 _P3). auto => />.
seq 2 2 : (={out, in_0, pub_seed, addr, buf, aux, addr_as_bytes, bitmask}); 1:inline*;auto.
seq 1 1 : (#pre); 1:call addr_to_bytes_hop1;auto.
seq 1 1 : (#pre).
  + exists * (init (fun (i_0 : int) => bitmask{1}.[0 + i_0]))%Array32, addr_as_bytes{1}, pub_seed{1}.               
    elim * => _P1 _P2 _P3. call {1} (prf_hop1 _P1 _P2 _P3). auto => />.
seq 1 1 : (#pre /\ ={bitmask}); 1:auto.
seq 1 1 : (#pre); 1:inline*;auto.
seq 1 1 : (#pre); 1:call addr_to_bytes_hop1;auto.
seq 1 1 : (#pre).
  + exists * (init (fun (i_0 : int) => bitmask{1}.[32 + i_0]))%Array32, addr_as_bytes{1}, pub_seed{1}.               
    elim * => _P1 _P2 _P3. call {1} (prf_hop1 _P1 _P2 _P3). auto => />.
seq 1 1 : (#pre); 1:auto.
sp.
seq 1 1 : (={buf,addr}); last first.
  + inline M(Syscall)._core_hash_128. wp ; sp.
      ecall {1} (hash_128_hop1 in_00{1}). auto => />.
while (
  ={out, in_0, pub_seed, addr, buf, aux, addr_as_bytes, bitmask} /\ (* #pre but without i{1,2} = W64.zero *)
  0 <= to_uint i{1} <= 2 * 32 /\
  ={i}
).
    + auto => /> &2 *. smt(@W64).
    + auto => />.
qed.

lemma hash_message_hop1 : 
    equiv[M(Syscall).__hash_message ~ M_Hop1(Syscall).__hash_message :
        ={arg, Glob.mem} ==> ={res, Glob.mem}].
proof.
proc.
seq 2 2 : (={Glob.mem, mhash, r, root, idx, m_with_prefix_ptr, mlen, buf, buf_n}); 1:auto.
seq 2 2 : (#pre /\ ={offset}); 1:inline*;sim => />.
seq 10 10 : (#pre /\ ={len}); 1:inline*;sim => />.
inline M(Syscall).__core_hash_in_ptr_ M(Syscall)._core_hash_in_ptr; wp; sp.
ecall {1} (hash_ptr_hop1 in_ptr0{1} inlen0{1}).
auto => />.
qed.

(*** WOTS ***)

lemma expand_seed_hop1 : 
    equiv [M(Syscall).__expand_seed ~ M_Hop1(Syscall).__expand_seed : ={arg} ==> ={res}].
proof.
proc.
seq 2 2 : (#pre /\ ={buf, ith_seed}); 1:auto.
seq 2 2 : (#pre /\ ={addr}); 1:inline*;auto.
seq 1 1 : (#pre /\ ={aux}); 1:call (_x_memcpy_u8u8_32_32_hop1);auto.
seq 1 1 : (#pre /\ ={buf}); 1:auto.
while (
  0 <= i{1} <= 67 /\ 
  ={i, ith_seed, addr, outseeds, buf, inseed}
); last by auto => />.
seq 4 4 : (#pre); last first.
    + seq 1 1 : (#pre /\ ={ith_seed, inseed}); last by auto => /> /#.
      ecall {1} (prf_keygen_hop1 buf{1} inseed{1}); auto => />.
seq 1 1 : (#pre); 1:inline;auto=>/>.
call addr_to_bytes_hop1.
auto => />.
qed.

lemma base_w_3_2_hop1 :
    equiv[M(Syscall).__base_w_3_2 ~ M_Hop1(Syscall).__base_w_3_2 : ={arg}  ==> ={res}].
proof. proc ; sim => />. qed.

lemma base_w_67_32_hop1 :
    equiv[M(Syscall).__base_w_67_32 ~ M_Hop1(Syscall).__base_w_67_32 : ={arg}  ==> ={res}].
proof. proc ; sim => />. qed.

lemma csum_hop1 :
    equiv[M(Syscall).__csum ~ M_Hop1(Syscall).__csum : ={arg} ==> ={res}].
proof. proc ; sim => />. qed. 

lemma checksum_hop1 :
    equiv[M(Syscall).__wots_checksum ~ M_Hop1(Syscall).__wots_checksum : ={arg} ==> ={res}].
proof.
proc.
sim => />.
qed.

lemma chain_lengths_hop1 :
    equiv [M(Syscall).__chain_lengths ~ M_Hop1(Syscall).__chain_lengths : ={arg} ==> ={res}].
proof.
proc.
seq 1 1 : (#pre /\ ={t}); 1:auto.
seq 1 1 : (#pre /\ ={lengths}); 1:call base_w_67_32_hop1;auto.
seq 1 1 : (#pre); 1:auto.
seq 1 1 : (#pre); 1:call checksum_hop1;auto.
qed.

lemma gen_chain_inplace_hop1 :
    equiv [M(Syscall).__gen_chain_inplace_ ~ M_Hop1(Syscall).__gen_chain_inplace_ : ={arg} ==> ={res}].
proof.
proc ; auto => />.
inline M(Syscall)._gen_chain_inplace M_Hop1(Syscall)._gen_chain_inplace.
inline M(Syscall).__gen_chain_inplace  M_Hop1(Syscall).__gen_chain_inplace.
seq 15 15 : (#pre /\ ={start1, start0, addr0, addr1, steps0, steps1, out0, out1, pub_seed0, pub_seed1}); 1:auto => />.
wp; sp.
while (
  ={out, start, steps, pub_seed, addr, i, t, start1, steps1, out0, out1, addr1, pub_seed1, pub_seed0}
); last first.
    + auto => />.
    + auto => />. seq 1 1 : (#pre); 1:inline;auto=>/>.
      inline M(Syscall).__thash_f_ M_Hop1(Syscall).__thash_f_.
      inline M(Syscall)._thash_f M_Hop1(Syscall)._thash_f. wp;sp.
      call thash_f_hop1; auto => />.      
qed.


lemma gen_chain_inplace_2_hop1 :
    equiv [M(Syscall).__gen_chain_inplace_ ~ M_Hop1(Syscall).__gen_chain_inplace_ : ={arg} ==> ={res}].
proof.
proc ; auto => />.
inline M(Syscall)._gen_chain_inplace M_Hop1(Syscall)._gen_chain_inplace.
inline M(Syscall).__gen_chain_inplace  M_Hop1(Syscall).__gen_chain_inplace.
seq 15 15 : (#pre /\ ={start1, start0, addr0, addr1, steps0, steps1, out0, out1, pub_seed0, pub_seed1}); 1:auto => />.
wp; sp.
while (
  ={out, start, steps, pub_seed, addr, i, t, start1, steps1, out0, out1, addr1, pub_seed1, pub_seed0}
); last first.
    + auto => />.
    + auto => />. seq 1 1 : (#pre); 1:inline;auto=>/>.
      inline M(Syscall).__thash_f_ M_Hop1(Syscall).__thash_f_.
      inline M(Syscall)._thash_f M_Hop1(Syscall)._thash_f. wp;sp.
      call thash_f_hop1; auto => />.      
qed.

lemma wots_pkgen_hop1 :
    equiv [M(Syscall).__wots_pkgen ~ M_Hop1(Syscall).__wots_pkgen : ={arg} ==> ={res}].
proof.
proc.
seq 1 1 : (#pre /\ ={pk, addr}).
  + inline M(Syscall).__expand_seed_ M(Syscall)._expand_seed M_Hop1(Syscall).__expand_seed_  M_Hop1(Syscall)._expand_seed. wp ; sp. call expand_seed_hop1. auto.
sp. 
while (={i,pk,pub_seed,addr} /\ 0 <= i{1} <= 67); last by auto.
seq 1 1 : (#pre /\ ={chain}); 1:auto.
seq 1 1 : (#pre); 1:inline;auto.
call {1} (gen_chain_inplace_hop1).
auto => /> /#.
qed.

lemma wots_sign_hop1 :
    equiv [M(Syscall).__wots_sign ~ M_Hop1(Syscall).__wots_sign : ={arg} ==> ={res}].
proof.
proc.
seq 2 2 : (={sig, msg, seed, pub_seed, addr, lengths}).
  + inline M(Syscall).__chain_lengths_ M(Syscall)._chain_lengths 
           M_Hop1(Syscall).__chain_lengths_ M_Hop1(Syscall)._chain_lengths; wp ; sp.
    call chain_lengths_hop1. auto => />.
seq 1 1 : (#pre). 
  + inline M(Syscall).__expand_seed_ M(Syscall)._expand_seed
           M_Hop1(Syscall).__expand_seed_ M_Hop1(Syscall)._expand_seed; wp ; sp.
    call expand_seed_hop1. auto.
sp.
while (={sig, msg, seed, pub_seed, addr, lengths, i} /\ 0 <= i{1} <= 67); last by skip => />.
seq 2 2 : (#pre /\ ={chain,addr}); 1:inline;auto.
seq 1 1 : (#pre /\ ={aux_0, aux_1}); 1:call {1} (gen_chain_inplace_hop1);auto => />. 
auto => /> /#.
qed.

lemma wots_pk_from_sig_hop1 :
    equiv [M(Syscall).__wots_pk_from_sig ~ M_Hop1(Syscall).__wots_pk_from_sig : 
      ={arg,Glob.mem} ==> ={res}].
proof.
proc.
sp.
seq 1 1 : (={pk, sig_ptr, msg, pub_seed, addr, lengths, Glob.mem}).
  + inline M(Syscall).__chain_lengths_ M(Syscall)._chain_lengths
           M_Hop1(Syscall).__chain_lengths_ M_Hop1(Syscall)._chain_lengths; wp ; sp.
    call chain_lengths_hop1. auto => />.
sp.
while (={pk, sig_ptr, msg, pub_seed, addr, lengths, i, Glob.mem} /\ 0 <= i{1} <= 67); last by skip => />. 
seq 1 1 : (#pre /\ ={chain}); 1:auto.
seq 1 1 : (#pre /\ ={addr}); 1:inline*;auto.
seq 3 3 : (#pre /\ ={start,steps}); 1:auto.
seq 2 2 : (#pre /\ ={t}); 1:auto.
seq 1 1 : (#pre /\ ={aux_0}).
  + call _x_memcpy_u8u8p_hop1. auto => /> .
seq 1 1 : (#pre); 1:auto => />.
auto => />. (* Simplify #post *)
seq 1 1 : (#pre /\ ={aux_1}).
  + call gen_chain_inplace_hop1; auto => />.
auto => /> /#.
qed.

(*** XMSS COMMONS ***)

lemma ltree_hop1 :
    equiv [M(Syscall).__l_tree ~ M_Hop1(Syscall).__l_tree :
      ={arg, Glob.mem} ==> ={res, Glob.mem}].
proof.
proc.
wp; sp.
seq 1 1 : (#pre).
  + inline;auto.
seq 1 1 : (#post);last first. (* isto isola o while [que vai ser o segundo subgoal] *)
  + call _x_memcpy_u8u8_32_32_hop1; auto =>/>.
while (
  ={buf0, buf1, l, height, leaf, wots_pk, pub_seed, addr, Glob.mem}
); last by auto => />. 
seq 2 2 : (#pre /\ ={parent_nodes}); 1:auto.
seq 2 2 : (={buf0, buf1, l, height, leaf, wots_pk, pub_seed, addr, Glob.mem}). (* Isto isola o primeiro while *)
    + while (#pre /\ ={i}); last by auto => />.
      seq 1 1 : (#pre /\ ={tree_index}); 1:auto=>/>.
      seq 1 1 : (#pre); 1:inline;auto=>/>.
      seq 2 2 : (#pre /\ ={offset_in, bytes}); 1:auto=>/>.
      seq 1 1 : (#pre /\ ={buf0}); 1:call memcpy_u8u8_2_1_hop1; auto => />.
      seq 3 3 : (#pre /\ ={bytes}); 1:auto => />.
      seq 1 1 : (#pre /\ ={buf1}); 1:call memcpy_u8u8_2_2_hop1; auto => />.
      seq 1 1 : (#pre); 1:call _thash_h_hop1; auto => />.
      seq 1 1 : (#pre /\ ={offset_out}); 1:auto => />.
      call memcpy_offset_hop1. auto => />.
    + seq 2 2 : (#pre /\ ={t}); 1:auto=> />.
      if; first by auto => />.
          (* first subgoal of if *)
          - seq 6 6 : (#pre /\ ={offset_out, offset_in}); 1:auto=> />.
            seq 2 2 : (#pre). (* isto isola o while *)
               * while (={j, wots_pk, offset_in, offset_out}); last by auto => />. auto => />.
            seq 3 3 : (#pre); 1:auto => />.
            inline; auto => />.
          (* second subgoal of if *) 
          - seq 2 2 : (#pre); 1: auto => /> *. 
            inline ; auto => />.
qed.

lemma compute_root_hop1 :
  equiv [M(Syscall).__compute_root ~ M_Hop1(Syscall).__compute_root :
      ={arg,Glob.mem} ==> ={res, Glob.mem}].
proof.
proc.
seq 5 5 : (={root, leaf, leaf_idx, _auth_path_ptr, pub_seed, addr, buffer, thash_in, auth_path_ptr, t32, Glob.mem}); 1:auto=>/>.
seq 1 1 : (#pre /\ ={buffer, aux}). (* Isola o primeiro if *)
  + if; first by auto => />.
      (* Second subgoal of if *)
       seq 1 1 : (#pre /\ ={aux}); 1:call _x_memcpy_u8u8_32_32_hop1; auto => />.
       seq 1 1 : (#pre); 1:auto => />.
       call _x_memcpy_u8u8p_hop1. auto => />.
      (* Last subgoal of if *)
      - seq 1 1 : (#pre); 1:call _x_memcpy_u8u8_64_32_hop1; auto => />.
        seq 1 1 : (#pre /\ ={aux}); 1:call _x_memcpy_u8u8p_hop1; auto => />.
  + seq 1 1 : (#pre); 1:auto => />.
    seq 2 2 : (#pre). (* Isola o while *)
      - while (#pre /\ ={i}); last by auto => />.
        seq 1 1 : (#pre /\ ={tree_height}); 1:auto.
        seq 5 5 : (#pre); 1:inline;auto=>/>.
        if; first by auto => />. 
            * seq 1 1 : (#pre); 1:auto.
              seq 1 1 : (#pre /\ ={aux, aux_0}); 1:call _thash_h_hop1; auto => />.
              seq 2 2 : (#pre); 1:auto.
              call _x_memcpy_u8u8p_hop1. auto => />.
            (* Last subgoal of if *)
            * seq 1 1 : (#pre); 1:auto.
              seq 1 1 : (#pre /\ ={aux, aux_0}); 1:call _thash_h_hop1; auto => />.
              seq 2 2 : (#pre); 1:auto.
              call _x_memcpy_u8u8p_hop1. auto => />.
      - seq 3 3 : (#pre); 1:inline; auto => />.
        call _thash_h_hop1. auto => />.
qed.

lemma gen_leaf_wots_hop1 :
    equiv[M(Syscall).__gen_leaf_wots ~ M_Hop1(Syscall).__gen_leaf_wots :
      ={arg,Glob.mem} ==> ={res}].
proof.
proc.
seq 2 2 : (={Glob.mem, leaf, sk_seed, pub_seed, ltree_addr, ots_addr, pk, _0}); 1:auto.
seq 1 1 : (#pre /\ ={pk}); 1:call wots_pkgen_hop1;auto. 
seq 1 1 : (#pre).
  + inline M(Syscall).__l_tree_ M(Syscall)._l_tree
           M_Hop1(Syscall).__l_tree_ M_Hop1(Syscall)._l_tree. wp ; sp.
    call ltree_hop1;auto.
auto.
qed.

lemma gen_leaf_wots__hop1 :
    equiv[M(Syscall).__gen_leaf_wots_ ~ M_Hop1(Syscall).__gen_leaf_wots_ :
      ={arg,Glob.mem} ==> ={res}].
proof.
proc.
inline M(Syscall).__gen_leaf_wots_ M_Hop1(Syscall).__gen_leaf_wots_.
inline M(Syscall)._gen_leaf_wots M_Hop1(Syscall)._gen_leaf_wots.
wp; sp.
call gen_leaf_wots_hop1.
auto => />.
qed.

lemma set_result_hop1 : 
    equiv [M(Syscall).__set_result ~ M_Hop1(Syscall).__set_result :
      ={arg,Glob.mem} ==> ={res}].
proof. proc ; sim => />. qed.

lemma xmssmt_core_sign_open :
    equiv [M(Syscall).__xmssmt_core_sign_open ~ M_Hop1(Syscall).__xmssmt_core_sign_open :
      ={arg, Glob.mem} ==> ={res, Glob.mem}].
proof.
proc.
seq 13 13 : (={buf, leaf, ltree_addr, node_addr, ots_addr, root, wots_pk, sm_offset, pub_root,
         pub_seed, idx, Glob.mem, smlen, mlen_ptr, buf, sm_ptr, m_ptr, pk}); 1:auto.
seq 6 6 : (#pre); 1:inline* ; sim => />.
seq 3 3 : (#pre /\ ={t64}); 1:auto.
seq 7 7 : (#pre /\ ={offset_out, offset_in, bytes}); 1:inline*;sim => />.
seq 1 1 : (#pre); 1:call _x_memcpy_u8u8p_hop1;auto.
seq 4 4 : (#pre /\ ={idx_hash}); 1:auto.
seq 1 1 : (#pre).
  + call hash_message_hop1. skip => /> *.   
seq 2 2 : (#pre); 1:auto.
while (#pre /\ ={i}); last by auto => />.
seq 4 4: (#pre /\ ={idx_leaf}).
  + inline; auto => />.
seq 6 6 : (#pre); 1:inline; auto => />.
seq 3 3 : (#pre); 1:auto => />.
seq 1 1 : (#pre).
  + inline M(Syscall).__wots_pk_from_sig_ M_Hop1(Syscall).__wots_pk_from_sig_. wp; sp.
    call wots_pk_from_sig_hop1. auto => />.
seq 4 4 : (#pre); 1:inline; auto => />.
seq 1 1 : (#pre).
  + inline M(Syscall).__l_tree_ M(Syscall)._l_tree M_Hop1(Syscall).__l_tree_ M_Hop1(Syscall)._l_tree.
     wp; sp. call ltree_hop1. auto => />.
seq 4 4 : (#pre); 1:auto.
inline M(Syscall).__compute_root_ M(Syscall)._compute_root M_Hop1(Syscall).__compute_root_ M_Hop1(Syscall)._compute_root.
wp; sp. call compute_root_hop1. auto => />.
qed.

(*** XMSS CORE ***)
 
lemma treehash_array_hop1 :
    equiv[M(Syscall).__treehash_array ~ M_Hop1(Syscall).__treehash_array : 
        ={Glob.mem, arg} ==> ={res, Glob.mem}].
proof.
proc.
seq 19 19 : (={Glob.mem, root, auth_path, sk_seed, pub_seed, leaf_idx, subtree_addr,
             _stack, buf, buf2, heights, ltree_addr, node_addr, ots_addr, offset, idx, u}); 1:inline; sim.
while (#pre); last by auto => />.
seq 2 2 : (
  ={Glob.mem, root, auth_path, sk_seed, pub_seed, leaf_idx, subtree_addr,
      _stack, buf, buf2, heights, ltree_addr, node_addr, ots_addr, offset,
      idx, u}
); 1:inline;auto=>/>.
seq 2 2 : (#pre). (* isola o while *)
  + while (#pre /\ ={j}); auto => />.
seq 1 1 : (#pre).
  + inline M(Syscall).__gen_leaf_wots_ M(Syscall)._gen_leaf_wots M_Hop1(Syscall).__gen_leaf_wots_ M_Hop1(Syscall)._gen_leaf_wots.
    wp ; sp. call gen_leaf_wots_hop1. auto => />.
seq 2 2 : ( ={Glob.mem, root, auth_path, sk_seed, pub_seed, leaf_idx, subtree_addr,
      _stack, buf, buf2, heights, ltree_addr, node_addr, ots_addr, offset,
      idx, u}). (* isola o while e remove a parte que nao interessa da #pre *)
  + while (#pre /\ ={j}); auto => />.
seq 6 6 : (#pre /\ ={index, t}); 1:auto=>/>.
seq 1 1 : (#pre). (* Isola o if *)
  + if; 1,3:auto => />.
    - while (#pre /\ ={j}); auto => />.
seq 2 2 : (#pre /\ ={a,b}); 1:auto => />.
seq 1 1 : (#pre /\ ={cond}); 1:inline; auto => />. 
while (#pre /\ ={cond}); last by auto => />.
seq 12 12 : (#pre /\ ={tree_idx}); 1:inline; auto => />.
seq 3 3 : (#pre). (* isola o while *)
  + while (#pre /\ ={j, aux, buf2}); auto => />.
seq 1 1 : (#pre).
  + inline M(Syscall).__thash_h_ M(Syscall)._thash_h M_Hop1(Syscall).__thash_h_ M_Hop1(Syscall)._thash_h. 
    wp; sp. call _thash_h_hop1. auto => />.
seq 3 3 : (#pre); 1:auto=> />.
seq 2 2 : (#pre); first by while (#pre /\ ={j}); auto => />.
seq 12 12 : (#pre); 1:auto => />.
seq 1 1 : (#pre); last by inline;auto=>/>.
if.
  + auto => />.
  + seq 5 5 : (#pre /\ ={t64}); 1:auto => />.
    while (#pre /\ ={j}); auto => />.     
  + auto => />.
qed.


lemma xmssmt_core_sign_open_hop1 :
    equiv [M(Syscall).__xmssmt_core_sign_open ~ M_Hop1(Syscall).__xmssmt_core_sign_open :
      ={arg, Glob.mem} ==> ={res, Glob.mem}].
proof.
proc.
seq 13 13 : (={m_ptr, mlen_ptr, sm_ptr, smlen, pk, buf, leaf, ltree_addr, node_addr, ots_addr, pub_root,
               pub_seed, root, wots_pk, sm_offset, pub_root, idx, Glob.mem}); 1:auto => />.
seq 6 6 : (#pre /\ ={ots_addr, ltree_addr, node_addr}); 1:inline; sim => />.
seq 7 7 : (#pre /\ ={t64, idx, offset_out, offset_in, bytes}); 1:sim => />.
seq 8 8 : (#pre /\ ={idx_hash}); 1:sim => />.
seq 1 1 : (#pre). call hash_message_hop1. auto => />. 
seq 2 2 : (#pre); 1:auto.
while (#pre /\ ={i}); last first.
  + auto => />.
  + seq 13 13 : (#pre /\ ={idx_leaf}); 1:inline; auto => />.
    seq 1 1 : (#pre /\ ={wots_pk}).
     * inline M(Syscall).__wots_pk_from_sig_ M_Hop1(Syscall).__wots_pk_from_sig_. 
       wp; sp. call wots_pk_from_sig_hop1. auto => />.
    seq 4 4 : (#pre); 1:inline; auto => />.
    seq 1 1 : (#pre).
     * inline M(Syscall).__l_tree_ M(Syscall)._l_tree M_Hop1(Syscall).__l_tree_ M_Hop1(Syscall)._l_tree.
       wp; sp. call ltree_hop1. auto => />.
    seq 4 4 : (#pre); 1:auto.
    inline M(Syscall).__compute_root_ M(Syscall)._compute_root M_Hop1(Syscall).__compute_root_ M_Hop1(Syscall)._compute_root.
    wp; sp. call compute_root_hop1. auto => />.
qed.

lemma xmssmt_core_seed_keypair_hop1 :
    equiv[M(Syscall).__xmssmt_core_seed_keypair ~ M_Hop1(Syscall).__xmssmt_core_seed_keypair :
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
       M_Hop1(Syscall).__treehash_array_ M_Hop1(Syscall)._treehash_array.
wp ; sp.
call treehash_array_hop1.
skip => />.
qed.

lemma xmssmt_core_keypair_hop1 :
    equiv[M(Syscall).__xmssmt_core_keypair ~ M_Hop1(Syscall).__xmssmt_core_keypair :
      ={arg,Glob.mem} ==> ={res}].
proof.
proc.
seq 3 3 : (={pk, sk, Glob.mem, seed, seed_p}); 1:auto.
seq 1 1 : (#pre); 1:sim.
call xmssmt_core_seed_keypair_hop1.
skip => />.
qed.

lemma xmssmt_core_sign_hop1 :
    equiv [M(Syscall).__xmssmt_core_sign ~ M_Hop1(Syscall).__xmssmt_core_sign :
      ={Glob.mem, arg} ==> ={res, Glob.mem}].
proof.
proc.
seq 18 18 : (={Glob.mem, sk, sm_ptr, smlen_ptr, m_ptr, mlen, auth_path, buf, idx_bytes,
               ots_addr, pub_root, pub_seed, root, sig, sk_prf, sk_seed, t64, idx, exit_0}). 
  + inline; sim => />.
seq 1 1 : (={Glob.mem, sk, sm_ptr, smlen_ptr, m_ptr, mlen, auth_path, buf, idx_bytes,
      ots_addr, pub_root, pub_seed, root, sig, sk_prf, sk_seed, t64, idx, 
      exit_0}). (* isola o if *)
  + if; 1,3: by auto => />.
    seq 1 1 : (#pre /\ ={aux}).
      * call memset_u8_4_hop1; auto => />.
    seq 1 1 : (#pre); 1:auto.
    seq 1 1 : (#pre /\ ={aux_0}); 1:call memset_u8_128_hop1; auto => />.
seq 1 1 : (#pre); last by if; auto => />. 
if; 1,3 : by auto => />.
seq 1 1 : (#pre).
  + call _x_memcpy_u8pu8_4_hop1. auto => />.
seq 2 2 : (#pre); 1: auto => />.
seq 1 1 : (#pre /\ ={aux}).
  + call ull_to_bytes_4_hop1. auto => />.
seq 1 1 : (#pre); 1:auto=>/>.
seq 1 1 : (#pre).
  + call ull_to_bytes_32_hop1. auto => />.
seq 1 1 : (#pre); 1: auto => />.
seq 1 1 : (#pre). 
  + ecall {1} (prf_hop1 buf{1} idx_bytes{1} sk_prf{1}). auto => />.
seq 1 1 : (#pre).
  + call _x_memcpy_u8pu8_32_hop1. auto => />.
seq 1 1 : (#pre); 1:auto=>/>.
seq 2 2 : (#pre).
  + while (#pre /\ ={j});auto=>/>.
seq 3 3 : (#pre /\ ={idx_hash}); 1:auto.
seq 1 1 : (#pre /\ ={aux_2}).
  + inline M(Syscall).__hash_message_ M(Syscall)._hash_message M_Hop1(Syscall).__hash_message_ M_Hop1(Syscall)._hash_message. wp; sp.
    call hash_message_hop1. auto => />.
seq 3 3 : (#pre).
  + inline. auto => />.
while (#pre /\ ={i}); last by auto => />.
seq 9 9 : (#pre /\ ={idx_leaf}); 1:inline; auto => />.
seq 1 1 : (#pre).
  + inline M(Syscall).__wots_sign_  M(Syscall)._wots_sign M_Hop1(Syscall).__wots_sign_  M_Hop1(Syscall)._wots_sign. wp; sp.
    call wots_sign_hop1. auto => />.
seq 1 1 : (#pre /\ ={aux_1}); 1:auto=>/>.
seq 2 2 : (#pre).
  + while (#pre /\ ={j}); auto => />.
seq 4 4 : (#pre); 1: auto => />.
seq 2 2 : (#pre).
  + while (#pre /\ ={j}); auto => />.
seq 1 1 : (#pre).
  + inline M(Syscall).__treehash_array_ M(Syscall)._treehash_array M_Hop1(Syscall).__treehash_array_ M_Hop1(Syscall)._treehash_array. wp; sp.
    call treehash_array_hop1. auto => />.
while (#pre /\ ={j}); auto => />.
qed.

(*** XMSS ***)

lemma xmss_keypair_hop1 :
    equiv[M(Syscall).__xmss_keypair ~ M_Hop1(Syscall).__xmss_keypair :
      ={arg,Glob.mem} ==> ={res}].
proof.
proc.
seq 4 4 : (={Glob.mem, pk, sk, oid}); 1:auto.
seq 1 1 : (#pre /\ ={aux, aux_0}).
  + inline M(Syscall).__xmssmt_core_keypair_ M(Syscall)._xmssmt_core_keypair
           M_Hop1(Syscall).__xmssmt_core_keypair_ M_Hop1(Syscall)._xmssmt_core_keypair.
    wp ; sp. call xmssmt_core_keypair_hop1. skip => />.
sim.
qed.

lemma xmss_sign_hop1 :
    equiv[M(Syscall).__xmss_sign ~ M_Hop1(Syscall).__xmss_sign :
      ={arg, Glob.mem} ==> ={res, Glob.mem}].
proof.
proc.
seq 1 1 : (={sk, sm_ptr, smlen_ptr, m_ptr, mlen, aux, aux_0, Glob.mem}).
  + wp ; sp. call xmssmt_core_sign_hop1. auto => />. 
sim => />.
qed.
