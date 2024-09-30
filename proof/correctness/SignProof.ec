pragma Goals : printall.

require import AllCore List RealExp IntDiv Distr DList IntDiv.
from Jasmin require import JModel JArray.

require import Params Types Hash XMSS_MT_PRF.
require import XMSS_IMPL Parameters.

require import Repr2. 
require import Utils2.

require import Array4 Array8 Array32 Array64 Array68 Array96 Array132 Array136 Array352 Array2144.
require import WArray32 WArray96 WArray136.

require import Correctness_Address Correctness_Mem Correctness_Hash.
require import DistrUtils.

require import BitEncoding.
(*---*) import BitChunking.

require import StdBigop. 
(*---*) import Bigint.

(*

arg{1}.`1 => sk
arg{1}.`2 => sm_ptr (* pointer to signed message *)
arg{1}.`3 => smlen  (* length of signed message *)
arg{1}.`4 => m_ptr  (* pointer to message *)
arg{1}.`5 => mlen   (* length of the message *)

arg{2}.`1 => sk
arg{2}.`2 => msg
*)


op load_message (mem : global_mem_t) (ptr : W64.t) (mlen : W64.t) =
  mkseq (fun (i : int) => mem.[to_uint ptr + i]) (to_uint mlen).


lemma sign_correct (mem : global_mem_t) (_sk : xmss_sk, _sm_ptr _smlen_ptr _m_ptr _mlen : W64.t) :
    n = XMSS_N /\ 
    prf_padding_val = XMSS_HASH_PADDING_PRF /\ 
    padding_len = XMSS_PADDING_LEN =>
    equiv [
      M(Syscall).__xmssmt_core_sign ~ XMSS_MT_PRF.sign :
      Glob.mem{1} = mem /\
      Glob.mem{2} = mem /\

      arg{1}.`1 = DecodeSkNoOID _sk /\
      arg{1}.`2 = _sm_ptr /\
      arg{1}.`3 = _smlen_ptr /\
      arg{1}.`4 = _m_ptr /\
      arg{1}.`5 = _mlen  /\

      arg{2}.`1 =_sk /\
      arg{2}.`2 = load_message mem _m_ptr _mlen /\

      valid_ptr_i arg{1}.`5 2500 /\
      2^XMSS_FULL_HEIGHT - 1 <= to_uint sk{2}.`idx (* the maximum number of signatures was reached *)
      ==>
      res{1}.`2 <> W64.zero
    ].
proof.
rewrite /XMSS_N => [#] n_val ??.
proc => /=.

seq 11 5 : (
  #pre /\
  idx{2} = sk{2}.`Types.idx /\
  2^XMSS_FULL_HEIGHT - 1 <= to_uint idx{1} /\
  idx{2} = W32ofBytes (sub sk{1} 0 4) /\
  exit_0{1} = W8.zero
).
    + admit.
seq 7 0 : (#pre /\ to_uint idx{1} = to_uint idx{2}).
    + admit.
rcondt {1} 1.
    + auto => /> &hr ?? H0 H1 ? H2. 
      rewrite uleE of_uintK /(`<<`) // ifT //=.

admit.
qed.



lemma sign_correct (mem : global_mem_t) (_sk : xmss_sk, _sm_ptr _smlen_ptr _m_ptr _mlen : W64.t) :
    n = XMSS_N /\ 
    prf_padding_val = XMSS_HASH_PADDING_PRF /\ 
    padding_len = XMSS_PADDING_LEN =>
    equiv [
      M(Syscall).__xmssmt_core_sign ~ XMSS_MT_PRF.sign :
      Glob.mem{1} = mem /\
      Glob.mem{2} = mem /\

      arg{1}.`1 = DecodeSkNoOID _sk /\
      arg{1}.`2 = _sm_ptr /\
      arg{1}.`3 = _smlen_ptr /\
      arg{1}.`4 = _m_ptr /\
      arg{1}.`5 = _mlen  /\

      arg{2}.`1 =_sk /\
      arg{2}.`2 = load_message mem _m_ptr _mlen /\

      valid_ptr_i arg{1}.`5 2500 /\
      0 <= to_uint sk{2}.`idx < 2^XMSS_FULL_HEIGHT - 1 (* ensures that the maximum number of signatures was not yet reached *)
      ==>
(*      res{2}.`2 = DecodeSkNoOID res{2}.`1 *)
      false
    ].
proof.
rewrite /XMSS_N => [#] n_val ??.
proc => /=.
seq 13 5 : (
  #pre /\
  exit_0{1} = W8.zero /\
  ots_addr{1} = zero_addr /\
  
  idx{2} = sk{2}.`Types.idx /\
  idx{2} = W32ofBytes (sub sk{1} 0 4) /\

  address{2} = zero_addr /\
  root{2} = sk{2}.`sk_root /\
  sk_prf{2} = sk{2}.`Types.sk_prf /\

  idx_new{2} = idx{2} + W32.one
). 

    + inline {1} 13.
      inline {1} 12.
      wp.
      ecall {1} (zero_addr_res addr{1}).
      auto => /> *.
      split. 
         * rewrite /zero_addr tP => i?.
           rewrite get_setE // initiE //.
         * admit.
seq 1 0 : (#pre); first by admit.
seq 2 0 : (#pre /\ to_uint t64{1} = to_uint mlen{1} + XMSS_SIG_BYTES). (* 2500 = XMSS_SIG_BYTES *) 
    + auto => /> *; rewrite to_uintD of_uintK /#. 
seq 1 0 : #pre; first by admit. (* memories are no longer equal *)
seq 1 0 : (
  #pre /\ 
  to_uint idx{1} = to_uint (W32ofBytes (sub sk{1} 0 4)) /\
  to_uint idx{1} = to_uint sk{2}.`Types.idx
).
    + admit. (* Add lemma to Correctness Bytes *)
rcondf {1} 1.
    + auto => /> &hr ???H H0 ?? H1. 
      rewrite uleE of_uintK H1.  
      rewrite /XMSS_FULL_HEIGHT /= in H.
      rewrite /(`<<`) ifT // /= /#. 
rcondt {1} 1; first by auto => /> *; smt(@W8).
seq 1 0 : (#pre); first by admit. (* fix this *)
seq 4 0 : (#pre /\ sub sk{1} 0 4 = lenbytes_be32 idx_new{2} 4); first by admit.

swap {2} 2 - 1.
seq 1 1 : (
    #pre /\
    to_list idx_bytes{1} = val idx_bytes{2}
); first by admit. (* este idx e o original ou o que foi incrementado? ++> O original *)

seq 0 1 : (#pre /\ sk{1} = DecodeSkNoOID sk{2}). (* Isto nao e #pre *)
    + auto => /> &1 *; do split => />. 
        * admit.
        * rewrite to_uintD /#.
        * move => ?. rewrite /XMSS_FULL_HEIGHT /= to_uintD. admit.
        * admit.
        * admit.
        * admit.

seq 1 0 : (#pre /\ to_list sk_prf{1} = val sk_prf{2}).
    + auto => /> &1 &2 *.
      apply (eq_from_nth witness); first by rewrite valP n_val size_to_list.
      rewrite size_to_list => j?. 
      rewrite get_to_list initiE // => />.
      rewrite /DecodeSkNoOID get_of_list 1:/#.
      rewrite nth_cat !size_cat !valP n_val sizeW32toBytes /= ifT 1:/#.
      rewrite nth_cat !size_cat !valP n_val sizeW32toBytes /= ifT 1:/#.
      by rewrite nth_cat !size_cat !valP n_val sizeW32toBytes /= ifF 1:/#.

seq 1 1 : (#pre /\ to_list buf{1} = val _R{2}).
    + inline {1} M(Syscall).__prf_ M(Syscall)._prf; wp; sp.
      exists * in_00{1}, key0{1}; elim * => _P1 _P2; call {1} (prf_correctness _P1 _P2) => [/# |]. 
      skip => /> &1 &2  ???? H0 H1 H2 H3 H4 H5 H6; do split. 
        * rewrite H5 #smt:(@NBytes).
        * rewrite H6 #smt:(@NBytes).
        * by move => ???? ->.
admit.
qed.
