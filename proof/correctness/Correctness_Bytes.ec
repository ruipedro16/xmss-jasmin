pragma Goals : printall.

require import AllCore List RealExp IntDiv.
from Jasmin require import JModel.

require import XMSS_IMPL.

require import Array2 Array3 Array32.

require import Address Hash BaseW.
require import Termination.

require import Parameters.

require import Utils2 Repr2.

require import BitEncoding.
(*---*) import BitChunking.

require import StdBigop. 
(*---*) import Bigint.

import W4u8.Pack.
import W8u8.Pack.

(* This is not big endian *)
op W32toBytes    (x : W32.t) : W8.t list = to_list (W4u8.unpack8 x).

(* This is big endian *)
op W32toBytes_be (x : W32.t) : W8.t list = rev (to_list (W4u8.unpack8 x)).

(* This is not big endian *)
op W64toBytes    (x : W64.t) : W8.t list = to_list (W8u8.unpack8 x).

(* This is big endian *)
op W64toBytes_be (x : W64.t) : W8.t list = rev (to_list (W8u8.unpack8 x)).

(* drop the least significant byte *)
(* x is not big endian *)
op drop_msbyte (x : W8.t list) : W8.t list = behead x.

(* x is big endian *)
op drop_msbyte_be (x : W8.t list) : W8.t list = take (size x - 1) x.

lemma size_behead x :
    size (behead x) = 
       if (x = [<:'a>]) then 0 else size x - 1 by smt().
(* sem este <:'a> tenho o erro "the formula contains free type variables" *)

lemma size_drop_lsbyte (x : W8.t list) : 
    0 < size x =>
    size (drop_msbyte x) = size x - 1.
proof.
move => ?.
by rewrite size_behead ifF 1:/#.
qed.

lemma size_drop_msbyte_be (x : W8.t list) : 
    0 < size x =>
    size (drop_msbyte_be x) = size x - 1.
proof.
move => ?; rewrite size_take /#.
qed.

 
(** -------------------------------------------------------------------------------------------- **)

lemma ull_to_bytes2_post (x : W64.t, y : W32.t) :
  phoare[
    M(Syscall).__ull_to_bytes_2 : 
    arg.`2 = x /\ 
    to_uint x = to_uint y /\
    0 <= to_uint y < W32.max_uint 
    ==>
    to_list res = toByte y 2 ] = 1%r.
proof.
proc.
    admit.
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
admit.
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
