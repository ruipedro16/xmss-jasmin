pragma Goals : printall.

require import AllCore List RealExp IntDiv Distr DList IntDiv.
from Jasmin require import JModel JArray.

require import Types Params Parameters Address Hash WOTS LTree XMSS_MT_Types XMSS_MT_PRF.
require import XMSS_IMPL.

import AuthPath.


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

op load_buf (mem : global_mem_t) (ptr : W64.t) (inlen : W64.t) =
  mkseq (fun (i : int) => mem.[to_uint ptr + i]) (to_uint inlen).

op max_sig : int = 2 ^ h - 1.

(* 2500 = XMSS_SIG_BYTES *)
lemma verify_correct (_sk : W8.t Array132.t, _sm_ptr _smlen_ptr _m_ptr _mlen : W64.t) :
    equiv [
      M(Syscall).__xmssmt_core_sign ~ XMSS_MT_PRF.sign :
      valid_ptr_i arg{1}.`5 2500 /\
      0 <= to_uint sk{2}.`idx < 2^XMSS_FULL_HEIGHT - 1 (* ensures that the maximum number of signatures was not yet reached *)
      ==>
      true
    ].
proof.
proc.
swap {2} 5 -3.
seq 12 2 : (
  #pre /\
  exit_0{1} = W8.zero /\
  ots_addr{1} = zero_addr /\
  idx_new{2} = sk{2}.`Types.idx + W32.one
).
    + inline {1} M(Syscall).__zero_address_.
      wp; sp.
      ecall {1} (zero_addr_res addr{1}). 
      skip => />.  
seq 0 1 : (#pre /\ address{2} = zero_addr).
    + inline {1} M(Syscall).__zero_address_.
      auto => />.  
seq 1 0 : (
    valid_ptr_i mlen{1} 2500 /\
    0 <= to_uint sk{2}.`Types.idx &&
    to_uint sk{2}.`Types.idx < 2 ^ XMSS_FULL_HEIGHT - 1 /\
    exit_0{1} = W8.zero /\
    ots_addr{1} = set_type zero_addr 0 /\ 
    idx_new{2} = sk{2}.`Types.idx + W32.one /\
    address{2} = zero_addr
); first by inline {1}; auto => />. 
seq 0 2 : (
  #pre /\
  root{2} = sk{2}.`sk_root /\
  sk_prf{2} = sk{2}.`Types.sk_prf
); first by auto.

seq 1 0 : (
  #pre /\
  load_buf Glob.mem{1} (sm_ptr{1} + W64.of_int 2500) mlen{1} = load_buf Glob.mem{1} m_ptr{1} mlen{1}
).
    + admit.
seq 2 0 : (#pre /\ t64{1} = mlen{1} + (of_int 2500)%W64); first by auto.
seq 1 0 : (
  #pre /\ 
  loadW64 Glob.mem{1} (to_uint sm_ptr{1}) = t64{1}
).
    + auto => /> *.
      do split. 
           * admit.
           * admit.
swap {2} 2 -1.
admit.
qed.
