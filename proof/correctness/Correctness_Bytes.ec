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
  + rewrite get_to_list get_setE //=.
    rewrite nth_W64toBytes_ext //=.
    rewrite bits8_div //= (: to_uint x %/ 256 = 0) 1:/#.
    rewrite /truncateu8 to_uint_shr of_uintK //= (: to_uint x %/ 256 = 0) 1:/#.
    reflexivity.
have ->: j = 1 by smt().
rewrite get_to_list get_setE // ifF 1:/# get_setE //=.
rewrite /W64toBytes_ext nth_rev; first by rewrite size_mkseq /#.
by rewrite size_mkseq (: max 0 2 = 2) //= nth_mkseq //= bits8_div.
qed.

lemma ull_to_bytes_32_correct (x : W64.t) : 
    phoare [
      M(Syscall).__ull_to_bytes_32 :
      arg.`2 = x /\ 
      0 <= to_uint x < W64.max_uint
      ==> 
      to_list res = W64toBytes_ext x 32
    ] = 1%r.
proof.
proc => /=.
unroll 4; unroll 5; unroll 6; unroll 7; unroll 8; unroll 9; unroll 10.
unroll 11; unroll 12; unroll 13; unroll 14; unroll 15; unroll 16; unroll 17.
unroll 18; unroll 19; unroll 20; unroll 21; unroll 22; unroll 23; unroll 24.
unroll 25; unroll 26; unroll 27; unroll 28; unroll 29; unroll 30; unroll 31.
unroll 32; unroll 33; unroll 34; unroll 35.

rcondt 4; first by auto.
rcondt 7; first by auto.
rcondt 10; first by auto.
rcondt 13; first by auto.
rcondt 16; first by auto.
rcondt 19; first by auto.
rcondt 22; first by auto.
rcondt 25; first by auto.
rcondt 28; first by auto.
rcondt 31; first by auto.
rcondt 34; first by auto.
rcondt 37; first by auto.
rcondt 40; first by auto.
rcondt 43; first by auto.
rcondt 46; first by auto.
rcondt 49; first by auto.
rcondt 52; first by auto.
rcondt 55; first by auto.
rcondt 58; first by auto.
rcondt 61; first by auto.
rcondt 64; first by auto.
rcondt 67; first by auto.
rcondt 70; first by auto.
rcondt 73; first by auto.
rcondt 76; first by auto.
rcondt 79; first by auto.
rcondt 82; first by auto.
rcondt 85; first by auto.
rcondt 88; first by auto.
rcondt 91; first by auto.
rcondt 94; first by auto.
rcondt 97; first by auto.
rcondf 100; first by auto.

auto => /> &hr *; apply (eq_from_nth witness); first by rewrite size_to_list size_W64toBytes_ext.
rewrite size_to_list => j?.
rewrite nth_W64toBytes_ext //.
rewrite get_to_list !get_setE //.

have E: truncateu8 x = W8.of_int (to_uint x) by smt(@W8).

case (j = 0) => [-> | ?].
    + rewrite /truncateu8.
      do (rewrite to_uint_shr; first by rewrite of_uintK /=).
      rewrite !of_uintK /=.
      rewrite unpack8E initE ifF /#. 

case (j = 1) => [-> | ?].
    + rewrite /truncateu8.
      do (rewrite to_uint_shr; first by rewrite of_uintK /=).
      rewrite !of_uintK /=.
      rewrite unpack8E initE ifF /#.

case (j = 2) => [-> | ?].
    + rewrite /truncateu8.
      do (rewrite to_uint_shr; first by rewrite of_uintK /=).
      rewrite !of_uintK /=.
      rewrite unpack8E initE ifF /#.

case (j = 3) => [-> | ?].
    + rewrite /truncateu8.
      do (rewrite to_uint_shr; first by rewrite of_uintK /=).
      rewrite !of_uintK /=.
      rewrite unpack8E initE ifF /#.

case (j = 4) => [-> | ?].
    + rewrite /truncateu8.
      do (rewrite to_uint_shr; first by rewrite of_uintK /=).
      rewrite !of_uintK /=.
      rewrite unpack8E initE ifF /#.

case (j = 5) => [-> | ?].
    + rewrite /truncateu8.
      do (rewrite to_uint_shr; first by rewrite of_uintK /=).
      rewrite !of_uintK /=.
      rewrite unpack8E initE ifF /#.

case (j = 6) => [-> | ?].
    + rewrite /truncateu8.
      do (rewrite to_uint_shr; first by rewrite of_uintK /=).
      rewrite !of_uintK /=.
      rewrite unpack8E initE ifF /#.

case (j = 7) => [-> | ?].
    + rewrite /truncateu8.
      do (rewrite to_uint_shr; first by rewrite of_uintK /=).
      rewrite !of_uintK /=.
      rewrite unpack8E initE ifF /#.

case (j = 8) => [-> | ?].
    + rewrite /truncateu8.
      do (rewrite to_uint_shr; first by rewrite of_uintK /=).
      rewrite !of_uintK /=.
      rewrite unpack8E initE ifF /#.

case (j = 9) => [-> | ?].
    + rewrite /truncateu8.
      do (rewrite to_uint_shr; first by rewrite of_uintK /=).
      rewrite !of_uintK /=.
      rewrite unpack8E initE ifF /#.

case (j = 10) => [-> | ?].
    + rewrite /truncateu8.
      do (rewrite to_uint_shr; first by rewrite of_uintK /=).
      rewrite !of_uintK /=.
      rewrite unpack8E initE ifF /#.

case (j = 11) => [-> | ?].
    + rewrite /truncateu8.
      do (rewrite to_uint_shr; first by rewrite of_uintK /=).
      rewrite !of_uintK /=.
      rewrite unpack8E initE ifF /#.

case (j = 12) => [-> | ?].
    + rewrite /truncateu8.
      do (rewrite to_uint_shr; first by rewrite of_uintK /=).
      rewrite !of_uintK /=.
      rewrite unpack8E initE ifF /#.

case (j = 13) => [-> | ?].
    + rewrite /truncateu8.
      do (rewrite to_uint_shr; first by rewrite of_uintK /=).
      rewrite !of_uintK /=.
      rewrite unpack8E initE ifF /#.

case (j = 14) => [-> | ?].
    + rewrite /truncateu8.
      do (rewrite to_uint_shr; first by rewrite of_uintK /=).
      rewrite !of_uintK /=.
      rewrite unpack8E initE ifF /#.

case (j = 15) => [-> | ?].
    + rewrite /truncateu8.
      do (rewrite to_uint_shr; first by rewrite of_uintK /=).
      rewrite !of_uintK /=.
      rewrite unpack8E initE ifF /#.

case (j = 16) => [-> | ?].
    + rewrite /truncateu8.
      do (rewrite to_uint_shr; first by rewrite of_uintK /=).
      rewrite !of_uintK /=.
      rewrite unpack8E initE ifF /#.

case (j = 17) => [-> | ?].
    + rewrite /truncateu8.
      do (rewrite to_uint_shr; first by rewrite of_uintK /=).
      rewrite !of_uintK /=.
      rewrite unpack8E initE ifF /#.

case (j = 18) => [-> | ?].
    + rewrite /truncateu8.
      do (rewrite to_uint_shr; first by rewrite of_uintK /=).
      rewrite !of_uintK /=.
      rewrite unpack8E initE ifF /#.

case (j = 19) => [-> | ?].
    + rewrite /truncateu8.
      do (rewrite to_uint_shr; first by rewrite of_uintK /=).
      rewrite !of_uintK /=.
      rewrite unpack8E initE ifF /#.

case (j = 20) => [-> | ?].
    + rewrite /truncateu8.
      do (rewrite to_uint_shr; first by rewrite of_uintK /=).
      rewrite !of_uintK /=.
      rewrite unpack8E initE ifF /#.

case (j = 21) => [-> | ?].
    + rewrite /truncateu8.
      do (rewrite to_uint_shr; first by rewrite of_uintK /=).
      rewrite !of_uintK /=.
      rewrite unpack8E initE ifF /#.

case (j = 22) => [-> | ?].
    + rewrite /truncateu8.
      do (rewrite to_uint_shr; first by rewrite of_uintK /=).
      rewrite !of_uintK /=.
      rewrite unpack8E initE ifF /#.

case (j = 23) => [-> | ?].
    + rewrite /truncateu8.
      do (rewrite to_uint_shr; first by rewrite of_uintK /=).
      rewrite !of_uintK /=.
      rewrite unpack8E initE ifF /#.

case (j = 24) => [-> | ?].
    + rewrite /truncateu8.
      do (rewrite to_uint_shr; first by rewrite of_uintK /=).
      rewrite !of_uintK /=.
      rewrite bits8_div // /#.

case (j = 25) => [-> | ?].
    + rewrite /truncateu8.
      do (rewrite to_uint_shr; first by rewrite of_uintK /=).
      rewrite !of_uintK /=.
      rewrite bits8_div // /#.

case (j = 26) => [-> | ?].
    + rewrite /truncateu8.
      do (rewrite to_uint_shr; first by rewrite of_uintK /=).
      rewrite !of_uintK /=.
      rewrite bits8_div // /#.

case (j = 27) => [-> | ?].
    + rewrite /truncateu8.
      do (rewrite to_uint_shr; first by rewrite of_uintK /=).
      rewrite !of_uintK /=.
      rewrite bits8_div // /#.

case (j = 28) => [-> | ?].
    + rewrite /truncateu8.
      do (rewrite to_uint_shr; first by rewrite of_uintK /=).
      rewrite !of_uintK /=.
      rewrite bits8_div // /#.

case (j = 29) => [-> | ?].
    + rewrite /truncateu8.
      do (rewrite to_uint_shr; first by rewrite of_uintK /=).
      rewrite !of_uintK /=.
      rewrite bits8_div // /#.

case (j = 30) => [-> | ?].
    + rewrite /truncateu8.
      do (rewrite to_uint_shr; first by rewrite of_uintK /=).
      rewrite !of_uintK /=.
      rewrite bits8_div // /#.

case (j = 31) => [-> | /#].
    + rewrite /truncateu8 //= bits8_div // /#.
qed.

lemma ull_to_bytes_3_correct (x : W64.t) : 
    phoare [
      M(Syscall).__ull_to_bytes_3 :
      0 <= to_uint x <= 2^XMSS_FULL_HEIGHT /\
      arg.`2 = x 
      ==> 
      to_list res = W64toBytes_ext x 3
    ] = 1%r.
proof.
proc => /=.
unroll 4; unroll 5; unroll 6.
rcondt 4; first by auto.
rcondt 7; first by auto.
rcondt 10; first by auto.
rcondf 13; first by auto.
auto => /> &hr H0 H1.
apply (eq_from_nth witness); first by rewrite size_to_list size_W64toBytes_ext.
rewrite size_to_list => j?.
rewrite get_to_list !get_setE // nth_W64toBytes_ext //.
case (j = 0) => [-> | ?].
  + rewrite unpack8E /= bits8_div //=.
    rewrite /truncateu8 !to_uint_shr of_uintK //=; congr; smt(@IntDiv).
case (j = 1) => [-> | ?].
  + rewrite unpack8E /= bits8_div //=.
    rewrite /truncateu8 !to_uint_shr of_uintK //=; congr; smt(@IntDiv).
case (j = 2) => [-> | /#].
  + rewrite unpack8E /= bits8_div //=.
qed.

(** -------------------------------------------------------------------------------------------- **)

require import Bytes.

print bits2w.

op load_Word_ptr (mem : global_mem_t) (ptr : W64.t)  = 
  rev (load_buf mem ptr XMSS_INDEX_BYTES).


lemma bytes_to_ull_ptr_correct (mem : global_mem_t) (ptr : W64.t) :
    phoare[
      M(Syscall).__bytes_to_ull_ptr :
      valid_ptr ptr (of_int XMSS_INDEX_BYTES)%W64 /\ 
      arg=ptr 
      ==> 
      res = W64ofBytes_ext (load_buf mem ptr XMSS_INDEX_BYTES)
    ] = 1%r.
proof.
proc.
unroll 3; unroll 4; unroll 5.
rcondf 6; first by auto.
rcondt 5; first by auto.
rcondt 4; first by auto.
rcondt 3; first by auto. 
print bits8E.
auto => /> &hr *.
rewrite /XMSS_INDEX_BYTES.
search W64ofBytes_ext.

rewrite (: 63 = 2^6 - 1) 1:/# !and_mod //.
rewrite wordP => j?.
rewrite !to_uint_shl !of_uintK //=.
rewrite !get_to_uint (: (0 <= j < 64) = true) 1:/# /=.
rewrite !to_uint_shl; 1..3: by rewrite /truncateu8 of_uintK /=.
rewrite !to_uint_zeroextu64.
rewrite to_uint_truncateu8 of_uintK /=.
rewrite /XMSS_INDEX_BYTES.
rewrite /loadW8.
locate W64of_bytes_ext.
admit.
qed.

(** -------------------------------------------------------------------------------------------- **)

import W8u8.

lemma zeroextu64E (x : W32.t) :
    forall (i : int), 0 <= i < 32 => (zeroextu64 x).[i] = x.[i].
proof.
move => i?.
rewrite !get_to_uint (: 0 <= i < 32 = true) 1:/# (: 0 <= i < 64 = true) 1:/# /=.
by rewrite to_uint_zeroextu64.
qed.

lemma shl_zero (w0 : W32.t) : w0 `<<` W8.zero = w0.
proof.
rewrite /(`<<`) /(`<<<`).
rewrite wordP => ??.
by rewrite initiE.
qed.

lemma nth_EncodeIdx (idx : W32.t) (i : int):
    0 <= to_uint idx < 2 ^ XMSS_FULL_HEIGHT =>
    0 <= i < XMSS_INDEX_BYTES =>
    nth witness (EncodeIdx idx) i =
    (of_int (to_uint idx %/ 2 ^ (8 * (XMSS_INDEX_BYTES - (i + 1)))))%W8.
proof.
rewrite /XMSS_FULL_HEIGHT /XMSS_INDEX_BYTES /= => ??.
rewrite /EncodeIdx.
rewrite nth_W32toBytes_ext 1,2:/#.
rewrite get_unpack8 1:/#.
by rewrite bits8_div 1:/#.
qed.

lemma bytes_to_ull_correct (bytes : W8.t Array3.t) (idx : W32.t) : (* the array has the XMSS_IDX_BYTES *)
   phoare[ 
    M(Syscall).__bytes_to_ull : 
    arg = bytes /\
    0 <= to_uint idx < 2^20 /\
    to_list bytes = EncodeIdx idx
    ==> 
    to_uint res = to_uint (DecodeIdx (to_list bytes))
  ] = 1%r.
proof.
proc.
conseq (: _ ==> result = zeroextu64 (DecodeIdx (to_list bytes))).
  + auto => /> result *; split; last by rewrite to_uint_zeroextu64.       
    move => H.
    rewrite wordP => j?.
    rewrite get_to_uint (: 0 <= j < 64 = true) 1:/# //=.
    rewrite H get_to_uint (: 0 <= j < 64 = true) 1:/# //=.
    by rewrite to_uint_zeroextu64.

unroll 3; unroll 4; unroll 5.
rcondf 6; first by auto.
rcondt 5; first by auto.
rcondt 4; first by auto.
rcondt 3; first by auto.

auto => /> H0 H1 H2.
rewrite H2 EncodeIdxK.
- rewrite /XMSS_FULL_HEIGHT /= /#.
rewrite (: 63 = 2^6 - 1) 1:/# !and_mod //.
rewrite !to_uint_shl !of_uintK //=.
have ->: truncateu8 W64.zero = W8.zero by rewrite /truncateu8 /=.
have ->: truncateu8 ((of_int 16))%W64 = W8.of_int 16 by rewrite /truncateu8 of_uintK /=.
have ->: truncateu8 ((of_int 8))%W64 = W8.of_int 8 by rewrite /truncateu8 of_uintK /=.
rewrite wordP => i?.
rewrite !get_to_uint (: (0 <= i < 64) = true) 1:/# /=.
rewrite to_uint_zeroextu64.
have ->:  (zeroextu64 bytes.[2] `<<` W8.zero) = zeroextu64 bytes.[2] by rewrite /(`<<`) /(`<<<`) wordP => ??; rewrite initiE.
simplify.

rewrite !to_uint_orw_disjoint.

- admit.

- admit.

rewrite !to_uint_zeroextu64.
rewrite !to_uint_shl of_uintK //=.
rewrite to_uint_zeroextu64 /=.
do congr.
have ->: bytes.[0] = nth witness (EncodeIdx idx) 0 by rewrite -H2 -get_to_list.
have ->: bytes.[1] = nth witness (EncodeIdx idx) 1 by rewrite -H2 -get_to_list.
have ->: bytes.[2] = nth witness (EncodeIdx idx) 2 by rewrite -H2 -get_to_list.
rewrite nth_EncodeIdx 2:/#.
  - rewrite /XMSS_FULL_HEIGHT /= /#.
rewrite nth_EncodeIdx 2:/#.
  - rewrite /XMSS_FULL_HEIGHT /= /#.
rewrite nth_EncodeIdx 2:/#.
  - rewrite /XMSS_FULL_HEIGHT /= /#.
rewrite /XMSS_INDEX_BYTES /= /#.
qed.
