pragma Goals : printall.

require import AllCore List RealExp IntDiv.
from Jasmin require import JModel.

require import XMSS_IMPL.

require import Array2 Array3 Array32.

require import Address Hash BaseW.
require import Termination.

require import Parameters.

require import Utils2 Repr2 Bytes.

require import BitEncoding.
(*---*) import BitChunking.

require import StdBigop. 
(*---*) import Bigint.

import W4u8.Pack.
import W8u8.Pack.

lemma size_behead x :
    size (behead x) = 
       if (x = [<:'a>]) then 0 else size x - 1 by smt().

 
(** -------------------------------------------------------------------------------------------- **)

lemma ull_to_bytes2_post (x : W64.t, y : W32.t) :
  phoare[
    M(Syscall).__ull_to_bytes_2 : 
    arg.`2 = x /\ 
    0 <= to_uint x < W8.max_uint 
    ==>
    to_list res = W64toBytes_ext x 2
  ] = 1%r.
proof.
proc.
unroll 4; unroll 5.
rcondt 4; first by auto.
rcondt 7; first by auto.
rcondf 10; first by auto.
auto => /> &hr H0 H1. 
apply (eq_from_nth witness).
  + rewrite size_to_list /W64toBytes_ext size_rev size_mkseq /#.
rewrite size_to_list => j?.
case (j = 0) => [-> | ?].
  + rewrite get_to_list get_setE //= /(`>>`) /= /(`>>>`) /=.
    rewrite /W64toBytes_ext nth_rev; first by rewrite size_mkseq /#.
    rewrite size_mkseq nth_mkseq 1:/# /= (: max 0 2 = 2) //=.
    rewrite bits8_div //.
    rewrite wordP => w?.
    rewrite /truncateu8; congr; congr.
    admit.
have ->: j = 1 by smt().
rewrite get_to_list get_setE // ifF 1:/# get_setE //=.
rewrite /W64toBytes_ext nth_rev; first by rewrite size_mkseq /#.
by rewrite size_mkseq (: max 0 2 = 2) //= nth_mkseq //= bits8_div.
qed.

lemma ull_to_bytes_32_correct (x : W64.t) : 
    phoare [
      M(Syscall).__ull_to_bytes_32 :
      arg.`2 = x 
      ==> 
      to_list res = toByte (truncateu32 x) XMSS_N
    ] = 1%r.
proof.
proc => /=.
admit.
qed.

lemma ull_to_bytes_3_correct (x : W64.t) : 
    phoare [
      M(Syscall).__ull_to_bytes_3 :
      0 <= to_uint x <= 2^XMSS_FULL_HEIGHT =>
      arg.`2 = x 
      ==> 
      to_list res = EncodeIdx (truncateu32 x)
    ] = 1%r.
proof.
proc => /=.
unroll 4; unroll 5; unroll 6.
rcondt 4; first by auto.
rcondt 7; first by auto.
rcondt 10; first by auto.
rcondf 13; first by auto.
auto => /> &hr H0.
apply (eq_from_nth witness).
  + rewrite size_to_list; admit.
rewrite size_to_list => j?.
rewrite get_to_list.
rewrite !get_setE //.
case (j = 0) => [-> | ?].
  + admit.
case (j = 1) => [-> | ?].
  + admit.
case (j = 2) => [-> | ?].
  + admit.
smt(). 
qed.
        


(** -------------------------------------------------------------------------------------------- **)

lemma _bytes_to_ull_ptr_correct (mem : global_mem_t) (ptr : W64.t) :
    hoare[
      M(Syscall).__bytes_to_ull_ptr :
      valid_ptr_i ptr 4 /\ arg=ptr 
      ==> 
      res = W64ofBytes (mkseq (fun i => loadW8 mem (to_uint ptr + i)) 4)
    ].
proof.
proc => /=.
while (
  #pre /\
  0 <= to_uint i <= 4 (* /\ ?????? *)
).
    + admit.
    + admit.
qed.

lemma bytes_to_ull_ptr_correct (mem : global_mem_t) (ptr : W64.t) :
    phoare[
      M(Syscall).__bytes_to_ull_ptr :
      valid_ptr_i ptr XMSS_INDEX_BYTES /\ arg=ptr 
      ==> 
      res = W64ofBytes (mkseq (fun i => loadW8 mem (to_uint ptr + i)) XMSS_INDEX_BYTES)
    ] = 1%r.
proof.
admit.
qed.

(** -------------------------------------------------------------------------------------------- **)


lemma ull_to_bytes_correct (bytes : W8.t Array3.t) : (* the array has the size XMSS_IDX_BYTES *)
   phoare[ 
    M(Syscall).__bytes_to_ull : 
    arg = bytes 
    ==> 
    to_uint res = to_uint (DecodeIdx (to_list bytes))
  ] = 1%r.
proof.
admit.
qed.
