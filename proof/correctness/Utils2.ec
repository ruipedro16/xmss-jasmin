pragma Goals : printall.

require import AllCore List RealExp IntDiv.
require import BitEncoding.
(*---*) import BitChunking.

from Jasmin require import JModel.

require import Params Address Hash LTree XMSS_MT_Types.

require import Array8 Array11.

(*****) import StdBigop.Bigint.

require import Bool.
import BS2Int.

require import W32One.

(* =================================================================================== *)


(* =================================================================================== *)

require import Array32.

lemma array_neq (x y : W8.t Array32.t) :
    to_list x <> to_list y <=> x <> y by smt(@Array32).    

lemma W32_one_0 : W32.one.[0] = true.
proof.
by rewrite /W32.one bits2wE initiE //= /int2bs nth_mkseq.
qed.

lemma lsb_even (w : W32.t) : 
    to_uint w %% 2 = 0 => w.[0] = false.
proof.
move => ?.
rewrite get_to_uint (: (0 <= 0 && 0 < 32) = true) //= /#.
qed.

lemma lsb_odd (w : W32.t) : 
    to_uint w %% 2 <> 0 => w.[0] = true.
proof.
move => ?.
rewrite get_to_uint (: (0 <= 0 && 0 < 32) = true) //= /#.
qed.


lemma L (w : W32.t) (i : int) :
     1 <= i < 32
  => to_uint w + 1 < W32.modulus
  => w.[0] = false
  => (w + W32.one).[i] = w.[i].
proof.
move=> rgi hlt w0E; rewrite get_to_uint.
have rgi0: 0 <= i < 32 = true by smt().
rewrite to_uintD_small // rgi0 /=.
rewrite get_to_uint to_uint_bits rgi0 /=.
do 4! congr; have ->: 2^i = 2 * 2^(i - 1).
- by rewrite -exprS 1:/#.
rewrite !divzMr 1?IntOrder.expr_ge0 ~-1://; 1,2: smt(@IntDiv).
do 2! congr; rewrite divzDl //.
rewrite /bits (mkseq_add _ 1 31) ~-1://.
rewrite bs2int_cat size_mkseq lez_maxr //=.
rewrite mkseq1 /= w0E dvdzD -1:dvdz_mulr //.
suff ->: bs2int [false] = 0 by rewrite dvdz0.
by rewrite /bs2int /= BIA.big_int1.
qed.


lemma xor1_even (x : W32.t) :
    0 <= to_uint x <= 2^20 => 
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
    0 <= to_uint x <= 2^10 => 
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
    0 <= i && i < size x %/ chunk_size =>
    nth witness (chunk chunk_size x) i = take chunk_size (drop (chunk_size * i) x).
proof.
move => ??; rewrite /chunk nth_mkseq //=. 
qed.

(* ar: address used for reading
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

lemma pow2_bound (a b: int) :
    0 <= a => 0 <= b =>  a <= b => 
    a <= 2^b
by smt(@IntDiv).

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

lemma pow2_c (e l : int) : 
    0 <= e < l =>
    0 < 2^e < 2^l.
proof.
move => [??].
split.
apply pow2_pos; first by assumption.
move => ?.
smt(@StdOrder.IntOrder).
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


lemma to_uint_W64_W32 (x0 : W64.t) (x1 : W32.t) :
    0 <= to_uint x0 < W32.max_uint /\
    0 <= to_uint x1 < W32.max_uint /\
    to_uint x0 = to_uint x1 =>
    x0 = zeroextu64 x1.
proof.
move => [#] *; smt(@W64).
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

lemma set_tree_addr_comp (x : W32.t Array8.t) (v1 v2 : int) :
    set_tree_addr (set_tree_addr x v1) v2 = set_tree_addr x v2.
proof.
rewrite /set_tree_addr tP => j?.
rewrite get_setE //.
case (j = 2) => *.
  + by rewrite get_setE // ifT //.
rewrite get_setE //.
case (j = 1) => *.
  + rewrite get_setE // ifF 1:/# get_setE // ifT //.
by do ! rewrite get_setE // ifF //.
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


(** -------------------------------------------------------------------------------------------- **)

lemma nbytes_eq:
  forall (s1 s2 : nbytes), val s1 = val s2 <=> s1 = s2
    by smt(@NBytes).

lemma auth_path_eq:
  forall (s1 s2 : auth_path), val s1 = val s2 <=> s1 = s2
    by smt(@AuthPath).

lemma len_n_bytes_eq : 
  forall (s1 s2 : len_nbytes), val s1 = val s2 <=> s1 = s2
    by smt(@LenNBytes).

(** -------------------------------------------------------------------------------------------- **)

lemma size_bits_to_bytes (bits : bool list) :
    size (BitsToBytes bits) = (size bits) %/ 8
        by rewrite /BitsToBytes size_map size_chunk.

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

lemma shl_zero (w0 : W32.t) : w0 `<<` W8.zero = w0.
proof.
rewrite /(`<<`) /(`<<<`).
rewrite wordP => ??.
by rewrite initiE.
qed.

lemma shr_zero (w0 : W32.t) : w0 `>>` W8.zero = w0.
proof.
rewrite /(`>>`) /(`>>>`).
rewrite wordP => ??.
by rewrite initiE.
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
