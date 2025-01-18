pragma Goals : printall.

require import AllCore List RealExp IntDiv.
require import BitEncoding.
require import Bool.
(*---*) import BitChunking.
(*---*) import StdBigop.Bigint.
(*---*) import BitEncoding.BS2Int.

from Jasmin require import JModel.

require import Params Address Hash LTree XMSS_MT_Types.

require import Array8 Array11.
import BS2Int.


(* =================================================================================== *)

lemma nth_singleton ['a] (dflt x : 'a) :
    nth dflt [x] 0 = x by smt().

lemma onewE i : W32.one.[i] = (i = 0).
proof.
rewrite /W32.one bits2wE initE /=.
by rewrite int2bs1 //= nth_nseq_if /#.
qed.

lemma W32_oneE : 
    forall (k : int), 0 < k < 32 => W32.one.[k] = false by smt(onewE). 

(* =================================================================================== *)

require import Array32.

lemma array_neq (x y : W8.t Array32.t) :
    to_list x <> to_list y <=> x <> y by smt(@Array32).    


lemma xor1_even (x : W32.t) :
    0 <= to_uint x <= W32.max_uint => 
    to_uint x %% 2 = 0 => 
    x `^` W32.one = x + W32.one.
proof.
move => /= ??.
have w0E : x.[0] = false by smt(lsb_even).
rewrite wordP => j?.
rewrite xorwE.
have E0: W32.one.[0] = true by rewrite /W32.one bits2wE initiE //= /int2bs nth_mkseq.
have E1: forall (k : int), 0 < k < 32 => W32.one.[k] = false by smt(W32_oneE).
case (j = 0) => [-> | ?].
  + rewrite E0 /=.
    rewrite eq_sym !get_to_uint.
    rewrite (: (0 <= 0 && 0 < 32) = true) 1:/# /=.
    rewrite to_uintD_small 1:/# /= /#.
rewrite E1 1:/# /=.
rewrite eq_sym get_to_uint.
have E: (0 <= j && j < 32) = true by smt().
rewrite to_uintD_small 1:/# E /=.
rewrite get_to_uint E /=.
do 4! congr.
have ->: 2^j = 2 * 2^(j - 1) by rewrite -exprS 1:/#. (* smt(@Real would also work *)
rewrite !divzMr 1?IntOrder.expr_ge0 ~-1://; 1,2: smt(@IntDiv).
do 2! congr; rewrite divzDl //.
qed.

lemma xor1_odd (x : W32.t) :
    0 <= to_uint x <= W32.max_uint => 
    to_uint x %% 2 <> 0 => 
    (x `^` W32.one) = x - W32.one.
proof.
move => /= ??.
have E0: W32.one.[0] = true by rewrite /W32.one bits2wE initiE //= /int2bs nth_mkseq.
have E1: forall (k : int), 0 < k < 32 => W32.one.[k] = false by smt(W32_oneE).
have E2 : x.[0] = true by smt(lsb_odd).
rewrite wordP => i?.
rewrite xorwE.
case (i = 0) => [-> | ?]; [rewrite E0 | rewrite E1 1:/#] => /=.
  + rewrite !get_to_uint (: (0 <= 0 && 0 < 32) = true) 1:/# /=.
    rewrite to_uintB 2:/# uleE /#.
rewrite !get_to_uint (: (0 <= i && i < 32) = true) 1:/# /=.
rewrite to_uintB /=; first by rewrite uleE /#.
do 4! congr.
have ->: 2^i = 2 * 2^(i - 1) by rewrite -exprS 1:/#. 
rewrite !divzMr 1?IntOrder.expr_ge0 ~-1://; 1,2: smt(@IntDiv).
do 2! congr => /#.
qed.

lemma nth_chunk ['a] (x : 'a list) (chunk_size i : int) :
    0 <= chunk_size =>
    0 <= i < size x %/ chunk_size =>
    nth witness (chunk chunk_size x) i = take chunk_size (drop (chunk_size * i) x).
proof.
move => ??; rewrite /chunk nth_mkseq //=. 
qed.

(* 
    ar: address used for reading
    aw: address used for writing 
*)
lemma load_store_mem (mem : global_mem_t) (ar aw : address) (val : W8.t) :
    loadW8 (storeW8 mem aw val) ar = (if ar = aw then val else mem.[ar]).
proof.
by rewrite /loadW8 /storeW8 get_setE.
qed.

lemma pow2_leq_1 (a : int): 
    0 <= a =>
    1 <= 2 ^ a.
proof.
smt(StdOrder.IntOrder.exprn_ege1).
qed.

(** -------------------------------------------------------------------------------------------- **)

lemma and_comm (a b : W32.t) : a `&` b = b `&` a by smt(@W32 pow2_32).

(** -------------------------------------------------------------------------------------------- **)

lemma sub_k (k : int) (a0 a1 : W32.t Array8.t) :
    0 <= k => sub a0 0 k = sub a1 0 k =>
      forall (i : int), 0 <= i < k => a0.[i] = a1.[i].
proof.
move => H0 H1 i Hi. 
have ->: a0.[i] = nth witness (sub a0 0 k) i by rewrite nth_sub.
by rewrite H1 nth_sub.
qed.

lemma sub_N (a1 a2: W32.t Array8.t) (len1 len2 : int) :
    0 <= len1 <= len2 =>
    sub a1 0 len2 = sub a2 0 len2 =>
    sub a1 0 len1 = sub a2 0 len1.
proof.
move => [H0 H1] H2.
apply (eq_from_nth witness); first by rewrite !size_sub /#.
rewrite size_sub // => i?.
have ?: forall (k : int), 0 <= k < len2 => a1.[k] = a2.[k] by smt(sub_k).
rewrite !nth_sub /#.
qed.

(** -------------------------------------------------------------------------------------------- **)

lemma truncate_1_and_63 :
    truncateu8 (W256.one `&` W256.of_int(63)) = W8.one
        by rewrite (: 63 = 2 ^ 6 - 1) 1:/# and_mod //=.


lemma shr_1 (x : W64.t) :
    to_uint (x `>>` W8.one) = to_uint x %/ 2
        by rewrite shr_div (: (to_uint W8.one %% 64) = 1) 1:#smt:(@W64) //=. 

lemma mod2_vals (x : int) :
    x %% 2 = 0 \/ x %% 2 = 1 by smt(). 

lemma fooT (x : W64.t):
    to_uint x %% 2 = 1 => W64.of_int (to_uint x %% 2) = W64.one by smt(@W64). 

lemma and_1_mod_2 (x : W64.t):
    x `&` W64.one <> W64.zero <=> to_uint x %% 2 = 1.
proof.
split; rewrite (: 1 = 2 ^ 1 - 1) 1:/# and_mod //=; [smt(fooT) |].
move => H.
rewrite fooT //= #smt:(@W64). 
qed.

(** -------------------------------------------------------------------------------------------- **)

lemma pow2_pos (e : int) :
    0 <= e => 0 < 2^e.
proof. move => ?; smt(@IntDiv). qed.

lemma pow2_neq_0  (t : int) : 
    0 <= t => 0 <> 2^t by smt(@Real).

lemma pow2_nonnegative ( t : int) :
    0 <= t => 0 <= 2^t.
proof.
elim t => //.
move => i??.
smt(@Real).
qed.


(** -------------------------------------------------------------------------------------------- **)

lemma to_uintW (i : int) : 
    0 <= i < W32.max_uint => 
    W64.of_int i = zeroextu64 (W32.of_int i).
proof.
move => ?; smt(@W64 @W32).
qed.

lemma to_uintW2 (i : int) : 
    0 <= i < W32.max_uint => 
    W32.of_int i = truncateu32 (W64.of_int i).
proof.
move => ?.
rewrite to_uintW //.
rewrite /truncateu32 to_uint_zeroextu64 of_uintK; smt(@W32 pow2_32).
qed.

(** -------------------------------------------------------------------------------------------- **)

op zero_addr : adrs = Array8.init (fun _ => W32.zero). 

lemma zero_addr_i :
    forall (k : int), 0 <= k < 8 => zero_addr.[k] = W32.zero.
proof.
move => k?.
rewrite /zero_addr initiE // /#.
qed.

lemma zero_addr_setZero :
    forall (k : int), 0 <= k < 8 => zero_addr.[k <- W32.zero] = zero_addr.
proof.
move => k?.
rewrite tP => j?.
rewrite get_setE //.
case (j = k) => // ?.
by rewrite zero_addr_i.
qed.

(** -------------------------------------------------------------------------------------------- **)

pred valid_ptr (p o : W64.t) = 
  0 <= to_uint o => 
    0 <= to_uint p /\ to_uint (p + o) < W64.modulus.

pred valid_ptr_i (p : W64.t) (o : int) = 
  0 <= o => 
    0 <= to_uint p /\ to_uint (p) + o < W64.modulus.

(*
 States that if a pointer p is valid for a certain length l1 and 
 l2 is a non-negative integer that is less than l1, then the pointer p 
 is also valid for the length l2
*)
lemma valid_ptr_sub (p : W64.t) (l1 l2 : int) :
    0 <= l1 => 
    valid_ptr_i p l1 =>
    l2 < l1 => 
    valid_ptr_i p l2 by smt().

pred valid_addr(p : int, o : int) = 
  0 <= o => 0 <= p /\ p + o < W64.modulus.

(** 
  This lemma asserts that two memory regions specified by their starting addresses and lengths are disjoint.
  
  Parameters:
  - p1 : int - The starting address of the first memory region.
  - l1 : int - The length of the first memory region.
  - p2 : int - The starting address of the second memory region.
  - l2 : int - The length of the second memory region.

  The lemma states that for all indices `k1` and `k2` within the bounds of their respective memory regions,
  the addresses `p1 + k1` and `p2 + k2` do not overlap, i.e., they are not equal.
**)
pred disjoint_ptr (p1 l1 p2 l2 : int) =
  forall (k1 : int), 0 <= k1 < l1 =>
    forall (k2 : int), 0 <= k2 < l2 =>
      p1 + k1 <> p2 + k2.

lemma disjoint_ptr_comm (p1 l1 p2 l2 : int) : 
    disjoint_ptr p1 l1 p2 l2 <=>
    disjoint_ptr p2 l2 p1 l1 by smt().

(* if p1 and p2 are disjoint, a sub region of p1 is also disjoint from p2 *)
lemma disjoint_ptr_sub (p1 l1 p2 l2 : int) l3 :
    disjoint_ptr p1 l1 p2 l2 => 
    l3 < l1 => 
    disjoint_ptr p1 l3 p2 l2 by smt().

(* if p1 and p2 are two disjoint memory regions, p1 and p2[0]/the ptr itself are disjoint *)
lemma disjoint_ptr_ptr (p1 l1 p2 l2 : int) : 
    disjoint_ptr p1 l1 p2 l2 =>
    0 < l2 =>
    forall (k : int), 0 <= k < l1 => p1 + k <> p2 by smt().

(* we can add an offset to the ptr if we remove it from the lengths *)
lemma disjoint_ptr_offset (p1 l1 p2 l2 o : int) :
    0 < o => 
    disjoint_ptr p1 l1 p2 l2 => 
    disjoint_ptr (p1 + o) (l1 - o) p2 l2 by smt().


(** -------------------------------------------------------------------------------------------- **)

require import Params.

lemma nbytes_eq:
  forall (s1 s2 : nbytes), val s1 = val s2 <=> s1 = s2
    by smt(@NBytes).

lemma auth_path_eq:
  forall (s1 s2 : auth_path), val s1 = val s2 <=> s1 = s2
    by smt(@AuthPath).

lemma len_n_bytes_eq : 
  forall (s1 s2 : len_nbytes), val s1 = val s2 <=> s1 = s2
    by smt(@LenNBytes).

lemma three_nbytes_eq :
  forall (s1 s2 : threen_bytes), val s1 = val s2 <=> s1 = s2 
    by smt(@ThreeNBytesBytes).

(** -------------------------------------------------------------------------------------------- **)

lemma nseq_nth (x : W8.t list) (i : int) (v : W8.t) :
    x = nseq i v => forall (k : int), 0 <= k < i => nth witness x k = v
        by smt(@List).

lemma size_nbytes_flatten (x : nbytes list) :
    size (flatten (map NBytes.val x)) = n * size x.
proof.
rewrite size_flatten sumzE BIA.big_map /(\o) //= -(StdBigop.Bigint.BIA.eq_big_seq (fun _ => n)) /=. 
  + move => *.
    have ?: forall (k : int), 0 <= k < size x => size (nth witness (map NBytes.val x) k) = n by move => *; rewrite (nth_map witness) 1:/# valP.
    smt(@List).
by rewrite big_constz count_predT size_map.
qed.

(** -------------------------------------------------------------------------------------------- **)

require import Array32 Array64.
require import Array131.

lemma sub_nth (a : W8.t Array64.t) (b : W8.t Array32.t) :
    sub a 0 32 = to_list b => 
       forall (k : int), 0 <= k < 32 => a.[k] = b.[k].
proof.
move => H k?.
by rewrite (: b.[k] = nth witness (to_list b) k) 1:/# -H nth_sub.
qed.

lemma ceil_3_2 : ceil (3%r / 2%r) = 2.
proof.
have ?: 1 < ceil (3%r / 2%r) by smt(@Real).
have ?: ceil (3%r / 2%r) <= 2 by smt(@Real).
smt().
qed.

lemma load_store_W64 (mem : global_mem_t) (a : address) (v : W64.t) :
    loadW64 (storeW64 mem a v) a = v.
proof.
rewrite /loadW64 /storeW64 wordP => j?.
rewrite pack8E /stores initiE // => />. 
rewrite initiE 1:/# => />. 
rewrite get_setE.
  + case (a + j %/ 8 = a + 7) => *; [rewrite /(\bits8) initiE /# |].
rewrite get_setE.
  + case (a + j %/ 8 = a + 6) => *; [rewrite /(\bits8) initiE /# |].
rewrite get_setE.
  + case (a + j %/ 8 = a + 5) => *; [rewrite /(\bits8) initiE /# |].
rewrite get_setE.
  + case (a + j %/ 8 = a + 4) => *; [rewrite /(\bits8) initiE /# |].
rewrite get_setE.
  + case (a + j %/ 8 = a + 3) => *; [rewrite /(\bits8) initiE /# |].
rewrite get_setE.
  + case (a + j %/ 8 = a + 2) => *; [rewrite /(\bits8) initiE /# |].
rewrite get_setE.
  + case (a + j %/ 8 = a + 1) => *; [rewrite /(\bits8) initiE /# |].
rewrite get_setE.
  + rewrite ifT 1:/# /(\bits8) initiE /#.
qed.

require import Bytes.
require import BaseW.

lemma nth_toByte_W64toBytes (w0 : W32.t) (w1 : W64.t) : 
    0 <= to_uint w1 < W32.max_uint =>
    to_uint w0 = to_uint w1 =>
    W64toBytes_ext w1 32 = toByte w0 32.
proof.
move => ?H.
apply (eq_from_nth witness); rewrite size_W64toBytes_ext // => [| j?]. 
  + by rewrite /toByte size_rev size_mkseq.
rewrite nth_W64toBytes_ext //.
rewrite /toByte nth_rev; first by rewrite size_mkseq /#.
rewrite size_mkseq (: max 0 32 = 32) 1:/# nth_mkseq 1:/# /=.
rewrite wordP => i?.
rewrite !get_to_uint (: 0 <= i < 8) //=.
case (0 <= 32 - (j + 1) && 32 - (j + 1) < 8) => [Ha | Hb].
  + rewrite get_unpack8 1:/# bits8_div 1:/# of_uintK.
case (0 <= 32 - (j + 1) && 32 - (j + 1) < 4) => [Haa | Hab].
  + by rewrite get_unpack8 1:/# bits8_div 1:/# of_uintK H.
rewrite unpack8E initE ifF 1:/#.
(* ------------------------------------------------------------------------------- *)
(*                              HA                                                    *)
(* ------------------------------------------------------------------------------- *)
(* TODO: melhorar isto. isto ta tudo martelado *)
case (j = 0) => [-> | ?].
    case (i = 0) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 1) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 2) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 3) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 4) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 5) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 6) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 7) => [-> | /#]; simplify; smt(@W32 pow2_32).
case (j = 1) => [-> | ?].
    case (i = 0) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 1) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 2) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 3) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 4) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 5) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 6) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 7) => [-> | /#]; simplify; smt(@W32 pow2_32).
case (j = 2) => [-> | ?].
    case (i = 0) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 1) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 2) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 3) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 4) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 5) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 6) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 7) => [-> | /#]; simplify; smt(@W32 pow2_32).
case (j = 3) => [-> | ?].
    case (i = 0) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 1) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 2) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 3) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 4) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 5) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 6) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 7) => [-> | /#]; simplify; smt(@W32 pow2_32).
case (j = 4) => [-> | ?].
    case (i = 0) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 1) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 2) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 3) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 4) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 5) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 6) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 7) => [-> | /#]; simplify; smt(@W32 pow2_32).
case (j = 5) => [-> | ?].
    case (i = 0) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 1) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 2) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 3) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 4) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 5) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 6) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 7) => [-> | /#]; simplify; smt(@W32 pow2_32).
case (j = 6) => [-> | ?].
    case (i = 0) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 1) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 2) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 3) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 4) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 5) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 6) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 7) => [-> | /#]; simplify; smt(@W32 pow2_32).
case (j = 7) => [-> | ?].
    case (i = 0) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 1) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 2) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 3) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 4) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 5) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 6) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 7) => [-> | /#]; simplify; smt(@W32 pow2_32).
case (j = 8) => [-> | ?].
    case (i = 0) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 1) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 2) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 3) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 4) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 5) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 6) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 7) => [-> | /#]; simplify; smt(@W32 pow2_32).
case (j = 9) => [-> | ?].
    case (i = 0) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 1) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 2) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 3) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 4) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 5) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 6) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 7) => [-> | /#]; simplify; smt(@W32 pow2_32).
case (j = 10) => [-> | ?].
    case (i = 0) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 1) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 2) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 3) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 4) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 5) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 6) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 7) => [-> | /#]; simplify; smt(@W32 pow2_32).
case (j = 11) => [-> | ?].
    case (i = 0) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 1) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 2) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 3) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 4) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 5) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 6) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 7) => [-> | /#]; simplify; smt(@W32 pow2_32).
case (j = 12) => [-> | ?].
    case (i = 0) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 1) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 2) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 3) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 4) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 5) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 6) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 7) => [-> | /#]; simplify; smt(@W32 pow2_32).
case (j = 13) => [-> | ?].
    case (i = 0) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 1) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 2) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 3) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 4) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 5) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 6) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 7) => [-> | /#]; simplify; smt(@W32 pow2_32).
case (j = 14) => [-> | ?].
    case (i = 0) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 1) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 2) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 3) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 4) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 5) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 6) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 7) => [-> | /#]; simplify; smt(@W32 pow2_32).
case (j = 15) => [-> | ?].
    case (i = 0) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 1) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 2) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 3) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 4) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 5) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 6) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 7) => [-> | /#]; simplify; smt(@W32 pow2_32).
case (j = 16) => [-> | ?].
    case (i = 0) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 1) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 2) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 3) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 4) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 5) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 6) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 7) => [-> | /#]; simplify; smt(@W32 pow2_32).
case (j = 17) => [-> | ?].
    case (i = 0) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 1) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 2) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 3) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 4) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 5) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 6) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 7) => [-> | /#]; simplify; smt(@W32 pow2_32).
case (j = 18) => [-> | ?].
    case (i = 0) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 1) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 2) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 3) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 4) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 5) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 6) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 7) => [-> | /#]; simplify; smt(@W32 pow2_32).
case (j = 19) => [-> | ?].
    case (i = 0) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 1) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 2) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 3) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 4) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 5) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 6) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 7) => [-> | /#]; simplify; smt(@W32 pow2_32).
case (j = 20) => [-> | ?].
    case (i = 0) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 1) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 2) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 3) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 4) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 5) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 6) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 7) => [-> | /#]; simplify; smt(@W32 pow2_32).
case (j = 21) => [-> | ?].
    case (i = 0) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 1) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 2) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 3) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 4) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 5) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 6) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 7) => [-> | /#]; simplify; smt(@W32 pow2_32).
case (j = 22) => [-> | ?].
    case (i = 0) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 1) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 2) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 3) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 4) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 5) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 6) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 7) => [-> | /#]; simplify; smt(@W32 pow2_32).
case (j = 23) => [-> | ?].
    case (i = 0) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 1) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 2) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 3) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 4) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 5) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 6) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 7) => [-> | /#]; simplify; smt(@W32 pow2_32).
case (j = 24) => [-> | ?].
    case (i = 0) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 1) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 2) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 3) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 4) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 5) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 6) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 7) => [-> | /#]; simplify; smt(@W32 pow2_32).
case (j = 25) => [-> | ?].
    case (i = 0) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 1) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 2) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 3) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 4) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 5) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 6) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 7) => [-> | /#]; simplify; smt(@W32 pow2_32).
case (j = 26) => [-> | ?].
    case (i = 0) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 1) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 2) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 3) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 4) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 5) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 6) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 7) => [-> | /#]; simplify; smt(@W32 pow2_32).
case (j = 27) => [-> | ?].
    case (i = 0) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 1) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 2) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 3) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 4) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 5) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 6) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 7) => [-> | /#]; simplify; smt(@W32 pow2_32).
case (j = 28) => [-> | ?].
    case (i = 0) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 1) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 2) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 3) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 4) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 5) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 6) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 7) => [-> | /#]; simplify; smt(@W32 pow2_32).
case (j = 29) => [-> | ?].
    case (i = 0) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 1) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 2) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 3) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 4) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 5) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 6) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 7) => [-> | /#]; simplify; smt(@W32 pow2_32).
case (j = 30) => [-> | ?].
    case (i = 0) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 1) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 2) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 3) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 4) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 5) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 6) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 7) => [-> | /#]; simplify; smt(@W32 pow2_32).
case (j = 31) => [-> | /#].
    case (i = 0) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 1) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 2) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 3) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 4) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 5) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 6) => [-> | ?]; first by simplify; smt(@W32 pow2_32).
    case (i = 7) => [-> | /#]; simplify; smt(@W32 pow2_32).

(* ------------------------------------------------------------------------------- *)
(*                                         HB                                      *)
(* ------------------------------------------------------------------------------- *)

rewrite unpack8E initE ifF 1:/#.
rewrite unpack8E initE ifF 1:/#.
reflexivity.
qed.
