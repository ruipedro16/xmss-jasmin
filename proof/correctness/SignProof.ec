pragma Goals : printall.

require import AllCore List RealExp IntDiv Distr DList IntDiv.
from Jasmin require import JModel JArray.

require import Types Params Parameters Address Notation Hash Primitives Wots XMSS_Commons XMSS_MT_PRF.
require import XMSS_IMPL.

require import Repr. 
require import Util Utils.

require import Array4 Array8 Array32 Array64 Array68 Array96 Array132 Array136 Array352 Array2144.
require import WArray32 WArray96 WArray136.

require import Correctness_Address Correctness_Mem Correctness_Hash.
require import Utils DistrUtils.

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

print mkseq. 


op load_message (mem : global_mem_t) (ptr : W64.t) (mlen : W64.t) =
  mkseq (fun (i : int) => mem.[to_uint ptr + i]) (to_uint mlen).


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

swap {2} 5 -4.

seq 12 1 : (
  #pre /\
  exit_0{1} = W8.zero /\
  ots_addr{1} = zero_addr /\
  address{2} = ots_addr{1}
); first by inline {1} M(Syscall).__zero_address_; wp; sp; ecall {1} (zero_addr_res addr{1}); skip => />. 

seq 2 0 : (#pre); first by admit. 

seq 2 0 : (#pre /\ to_uint t64{1} = to_uint mlen{1} + 2500). (* 2500 = XMSS_SIG_BYTES *) 
    + auto => /> &1 *; rewrite to_uintD of_uintK /#. 

rcondf {1} 3.
    + admit. 

qed.
