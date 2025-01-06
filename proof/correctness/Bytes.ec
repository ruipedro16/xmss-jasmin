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

