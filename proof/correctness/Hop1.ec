pragma Goals : printall.

(* Hop 1: The Jasmin program is equivalent to the Jasmin program replacing the prf 
          implementation with a prf operator *)

require import AllCore.

require import XMSS_IMPL XMSS_IMPL_PP.

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
proof.
proc ; inline ; sim.
qed.

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
sp.
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
       * call (addr_to_bytes_hop1). skip => /> &1 &2 *. admit.
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

lemma gen_chain_inplace_hop1 :
    equiv [M(Syscall).__gen_chain_inplace ~ Mp(SCall).__gen_chain_inplace :
      ={arg} ==> ={res}].
proof.
proc.
sp.
while (#pre).
admit.
admit.
qed.

lemma wots_pkgen_hop1 :
    equiv [M(Syscall).__wots_pkgen ~ Mp(SCall).__wots_pkgen : ={arg} ==> ={res}].
proof.
proc.
seq 1 1 : (#pre /\ ={pk, addr}).
  + inline M(Syscall).__expand_seed_ M(Syscall)._expand_seed Mp(SCall).__expand_seed_  Mp(SCall)._expand_seed. wp ; sp. call expand_seed_hop1. auto.
seq 1 1 : (#pre /\ ={i} /\ i{1}=0 /\ i{2}=0); 1: auto.
while (#pre /\  0 <= i{1} <= 67); last by auto.
seq 1 1 : (#pre /\ ={chain}); 1:auto.
seq 1 1 : (#pre); 1:inline;auto.
admit.
qed.
