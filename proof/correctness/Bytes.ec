pragma Goals : printall.

require import AllCore List RealExp IntDiv.

from Jasmin require import JModel.

op W32toBytes (x : W32.t) : W8.t list = rev (to_list (W4u8.unpack8 x)).
op W32ofBytes (x : W8.t list) : W32.t = W4u8.pack4 (rev x).

import W4u8.
import W8u8.

lemma W32toBytesK (x : W32.t) :
    W32ofBytes (W32toBytes x) = x.
proof.
rewrite /W32ofBytes /W32toBytes revK /#.
qed.

op W32toBytes_ext (x : W32.t) (l : int) : W8.t list = 
  rev (mkseq (fun i => nth W8.zero (to_list (W4u8.unpack8 x)) i) l).

lemma size_W32toBytes (x : W32.t) : 
    size (W32toBytes x) = 4.
proof.
by rewrite /W32toBytes size_rev size_to_list.
qed.

lemma size_W32toBytes_ext (w : W32.t) (l : int):
    0 < l => size (W32toBytes_ext w l) = l.
proof.
move => ?; rewrite /W32toBytes_ext size_rev size_mkseq /#.
qed.

lemma W32_toBytes_ext_out (dflt : W8.t) (w : W32.t) (l i : int) :
    0 < l =>
    ! (0 <= l - (i + 1) < 4) => 
    0 <= i < l =>
    nth dflt (W32toBytes_ext w l) i = W8.zero.
proof.
move => ???.
rewrite /W32toBytes_ext nth_rev; first by rewrite size_mkseq /#.
rewrite size_mkseq (: max 0 l = l) 1:/#.
rewrite nth_mkseq 1:/# /=.
rewrite unpack8E initE ifF //.
qed.


op W64toBytes (x : W64.t) : W8.t list = rev (to_list (W8u8.unpack8 x)).
op W64ofBytes (x : W8.t list) : W64.t = W8u8.pack8 (rev x).

lemma W64toBytesK (x : W64.t) :
    W64ofBytes (W64toBytes x) = x.
proof.
rewrite /W64ofBytes /W64toBytes revK /#.
qed.

lemma nth_W32toBytes_ext dflt (w : W32.t) (l i : int)  :
    0 < l => 
    0 <= i < l =>
    nth dflt (W32toBytes_ext w l) i = (unpack8 w).[l - (i + 1)]. 
proof.
move => ??.
rewrite /W32toBytes_ext nth_rev; first by rewrite size_mkseq /#.
rewrite size_mkseq (: max 0 l = l) 1:/# //=.
by rewrite nth_mkseq 1:/# get_to_list.
qed.


(* Igual ao toByte da spec *)
op W64toBytes_ext (x : W64.t) (l : int) : W8.t list = 
  rev (mkseq (fun i => nth W8.zero (to_list (W8u8.unpack8 x)) i) l). 

lemma size_W64toBytes :
    forall (x : W64.t), size (W64toBytes x) = 8.
proof.
by move => ?; rewrite /W64toBytes size_rev size_to_list.
qed.


lemma size_W64toBytes_ext (w : W64.t) (l : int) :
    0 < l => size (W64toBytes_ext w l) = l.
proof.
move => ?; rewrite /W64toBytes_ext size_rev size_mkseq /#.
qed.

lemma nth_W64toBytes_ext dflt (w : W64.t) (l i : int)  :
    0 < l => 
    0 <= i < l =>
    nth dflt (W64toBytes_ext w l) i = (unpack8 w).[l - (i + 1)]. 
proof.
move => ??.
rewrite /W64toBytes_ext nth_rev; first by rewrite size_mkseq /#.
rewrite size_mkseq (: max 0 l = l) 1:/# //=.
by rewrite nth_mkseq 1:/# get_to_list.
qed.

lemma nth_W64ofBytes (bytes : W8.t list) (i : int) :
    0 <= i < 64 => 
    0 <= i %/ 8 && i %/ 8 < size bytes =>
    (W64ofBytes bytes).[i] = bytes.[size bytes - (i %/ 8 + 1)].[i %% 8]. 
proof.
move => ??.
rewrite /W64ofBytes.
rewrite pack8E initiE //=.
rewrite of_listE initiE 1:/# /=.
by rewrite nth_rev 1:/#.
qed.


(* if a number fits in a W32.t, we can using a W64.t results in the same result *)

import BitEncoding.BS2Int.

lemma truncateu32E (x : W64.t) (i : int) :
    0 <= to_uint x < W32.max_uint =>
    0 <= i < 32 =>
    (truncateu32 x).[i] = x.[i].
proof.
move => /= ??. 
rewrite /truncateu32.
rewrite !get_to_uint.
rewrite (: (0 <= i && i < 32) = true) 1:/# (: (0 <= i && i < 64) = true) 1:/# /=.
rewrite of_uintK /=.
case (i = 0) => [-> /= /# | ?].
case (i = 1) => [-> /= /# | ?].
case (i = 2) => [-> /= /# | ?].
case (i = 3) => [-> /= /# | ?].
case (i = 4) => [-> /= /# | ?].
case (i = 5) => [-> /= /# | ?].
case (i = 6) => [-> /= /# | ?].
case (i = 7) => [-> /= /# | ?].
case (i = 8) => [-> /= /# | ?].
case (i = 9) => [-> /= /# | ?].
case (i = 10) => [-> /= /# | ?].
case (i = 11) => [-> /= /# | ?].
case (i = 12) => [-> /= /# | ?].
case (i = 13) => [-> /= /# | ?].
case (i = 14) => [-> /= /# | ?].
case (i = 15) => [-> /= /# | ?].
case (i = 16) => [-> /= /# | ?].
case (i = 17) => [-> /= /# | ?].
case (i = 18) => [-> /= /# | ?].
case (i = 19) => [-> /= /# | ?].
case (i = 20) => [-> /= /# | ?].
case (i = 21) => [-> /= /# | ?].
case (i = 22) => [-> /= /# | ?].
case (i = 23) => [-> /= /# | ?].
case (i = 24) => [-> /= /# | ?].
case (i = 25) => [-> /= /# | ?].
case (i = 26) => [-> /= /# | ?].
case (i = 27) => [-> /= /# | ?].
case (i = 28) => [-> /= /# | ?].
case (i = 29) => [-> /= /# | ?].
case (i = 30) => [-> /= /# | ?].
case (i = 31) => [-> /= /# | ?].
case (i = 32) => [-> /= /# | /#].
qed.

lemma W64toBytes_truncateu32 (x : W64.t) (l : int) : 
    0 <= to_uint x < W32.max_uint => 
    0 < l <= 4 =>
    W64toBytes_ext x l = W32toBytes_ext (truncateu32 x) l.
proof.
move => ??.
apply (eq_from_nth witness).
  + by rewrite size_W64toBytes_ext 1:/# size_W32toBytes_ext // /#.
rewrite size_W64toBytes_ext // 1:/# => j?.
rewrite /W64toBytes_ext /W32toBytes_ext.
do 2! (rewrite nth_rev; first by rewrite size_mkseq /#).
rewrite !size_mkseq (: max 0 l = l) 1:/# /=.
rewrite !nth_mkseq 1,2:/#.
rewrite !to_listE.
rewrite !nth_mkseq 1,2:/# /=.
rewrite get_unpack8 1:/# bits8E.
rewrite get_unpack8 1:/# bits8E.
rewrite wordP => i?.
rewrite !initiE //=.
rewrite truncateu32E // /#. 
qed.

require import Hash.

lemma W64toBytes_ext_toByte_64 (w : W64.t) (l : int) :
    W64toBytes_ext w l = toByte_64 w l.
proof.
by [].
qed.



lemma W32toBytes_zeroextu64 (x : W32.t) (l : int) : 
    0 <= to_uint x < W32.max_uint =>
    0 < l < 4 =>
    W32toBytes_ext x l = W64toBytes_ext (zeroextu64 x) l.
proof.
move => ??.
apply (eq_from_nth witness).
- rewrite size_W64toBytes_ext 1:/# size_W32toBytes_ext // /#.
rewrite size_W32toBytes_ext // 1:/# => j?.
rewrite W64toBytes_truncateu32 2:/#.
- by rewrite to_uint_zeroextu64.
do congr.
rewrite wordP => k?.
rewrite !get_to_uint.
rewrite to_uint_truncateu32 to_uint_zeroextu64.
have ->: to_uint x %% W32.modulus = to_uint x by smt(@W32 pow2_32).
reflexivity.
qed.
