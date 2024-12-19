pragma Goals : printall.

require import AllCore List RealExp IntDiv.
require import BitEncoding.
(*---*) import BitChunking.

from Jasmin require import JModel.

require import Params Address Hash LTree XMSS_MT_Types.

require import Array8 Array11.

(*****) import StdBigop.Bigint.


(** ----cenas de memorias --------------------------------------------------------------------- **)

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

lemma get_setE_to_list (a : W32.t Array11.t) (e : W32.t) (i j : int) :
    0 <= i < size (to_list a) =>
    a.[i <- e].[j] = nth witness (put (to_list a) i e) j.
proof.
rewrite size_to_list => ?.
rewrite nth_put.
  + by rewrite size_to_list. 
rewrite get_setE // get_to_list /#.
qed.


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


lemma addr_sub_5 (a0 a1 : W32.t Array8.t) :
    a0.[0] = a1.[0] /\
    a0.[1] = a1.[1] /\
    a0.[2] = a1.[2] /\
    a0.[3] = a1.[3] /\
    a0.[4] = a1.[4] 
          <=>
    sub a0 0 5 = sub a1 0 5.
proof.
split.
  + move => [#] *.
    apply (eq_from_nth witness); first by rewrite !size_sub.
    rewrite size_sub // => i?.
    rewrite !nth_sub //=/#.
  + move => H.
    do split.
       - have ->: a0.[0] = nth witness (sub a0 0 5) 0 by rewrite nth_sub.
         by rewrite H nth_sub.
       - have ->: a0.[1] = nth witness (sub a0 0 5) 1 by rewrite nth_sub.
         by rewrite H nth_sub.
       - have ->: a0.[2] = nth witness (sub a0 0 5) 2 by rewrite nth_sub.
         by rewrite H nth_sub.
       - have ->: a0.[3] = nth witness (sub a0 0 5) 3 by rewrite nth_sub.
         by rewrite H nth_sub.
       - have ->: a0.[4] = nth witness (sub a0 0 5) 4 by rewrite nth_sub.
         by rewrite H nth_sub.
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


op concatMap  (f: 'a -> 'b list) (a: 'a list): 'b list = flatten (map f a).

op W32ofBytes (bytes : W8.t list) : W32.t = W32.bits2w (concatMap W8.w2bits bytes).
op W64ofBytes (bytes : W8.t list) : W64.t = W64.bits2w (concatMap W8.w2bits bytes). (* isto ja faz zero ext *)
op W32toBytes (x : W32.t) : W8.t list = map W8.bits2w (chunk W8.size (W32.w2bits x)).


lemma foo (t : W8.t list) :
    0 < size t <= 4 => 
         forall (k : int), 32 <= k < 64 => (zeroextu64 (W32ofBytes t)).[k] = false.
proof.
move => ?k?.
rewrite /W32ofBytes zeroextu64E pack2E initiE 1:/# => />.
rewrite initiE 1:/# => />.
by rewrite ifF 1:/#.
qed.

lemma foo2 (t : W8.t list) :
    0 < size t <= 4 => 
         forall (k : int), 32 <= k < 64 => (W64ofBytes t).[k] = false.
proof.
move => ?k?.
rewrite /W64ofBytes /bits2w initiE 1:/# => />.
rewrite nth_out //. 
have ?: size (concatMap W8.w2bits t) <= 32.
  + rewrite /concatMap size_flatten. 
    rewrite sumzE BIA.big_map /(\o) //= -(StdBigop.Bigint.BIA.eq_big_seq (fun _ => 8)); last first.
        * rewrite big_constz count_predT size_map /#.
    auto => />.
    have ?: (forall (k : int), 0 <= k < size t => size (nth witness (map W8.w2bits t) k) = 8) by move => *; rewrite (nth_map witness).
    smt(@List).
smt(). 
qed.

lemma bar (t : W8.t list) :
    0 < size t <= 4 => 
         forall (k : int), 0 <= k < 32 => (zeroextu64 (W32ofBytes t)).[k] = (W64ofBytes t).[k].
proof.
move => ?k?.
rewrite /W32ofBytes /W64ofBytes zeroextu64E pack2E initiE 1:/# => />.
rewrite initiE 1:/# => />.
rewrite ifT 1:/# (: k %% 32 = k) 1:/#.
by rewrite !bits2wE initiE 1:/# initiE 1:/#.
qed.

lemma W64_W32_of_bytes (t : W8.t list) :
    0 < size t <= 4 => 
       zeroextu64 (W32ofBytes t) = W64ofBytes t.
proof.
move => H.
rewrite wordP => i?.

case (0 <= i < 32) => ?; first by apply bar.
rewrite foo // 1:/# foo2 // /#.
qed.

lemma W64_W32_of_bytes2 (t : W8.t list) : 
    0 < size t <= 4 => 
       to_uint (W32ofBytes t) = to_uint (W64ofBytes t).
proof.
move => ?.
by rewrite -W64_W32_of_bytes // to_uint_zeroextu64.
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

lemma size_lenbytes_be64 (val : W64.t, len : int) : 
    0 <= len =>
      size (lenbytes_be64 val len) = len.
proof.
move => ?.
rewrite /lenbytes_be64 size_rev size_mkseq /#.
qed.

lemma size_lenbytes_be32 (val : W32.t, len : int) : 
    0 <= len =>
      size (lenbytes_be32 val len) = len.
proof.
move => ?.
rewrite /lenbytes_be64 size_rev size_mkseq /#.
qed.

lemma sizeW32toBytes (x : W32.t) :
    size (W32toBytes x) = 4.
proof.
rewrite /W32toBytes size_map size_chunk // size_w2bits.
qed.


(** -------------------------------------------------------------------------------------------- **)

lemma nseq_nth (x : W8.t list) (i : int) (v : W8.t) :
    x = nseq i v => forall (k : int), 0 <= k < i => nth witness x k = v
        by smt(@List).

lemma size_singleton ['a] (x : 'a) : size [x] = 1 by [].


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


lemma sub_sub_minus (a b : W8.t Array131.t) (m n : int) :
    0 <= n < 131 /\ 0 <= m < n =>
       sub a 0 n = sub b 0 n => sub a 0 m = sub b 0 m.
proof.
move => [#] ????H.
apply (eq_from_nth witness); first by rewrite !size_sub.
rewrite size_sub // => i?.
rewrite !nth_sub //=.
have ->: a.[i] = nth witness (sub a 0 n) i by rewrite nth_sub // /#.
have ->: b.[i] = nth witness (sub b 0 n) i by rewrite nth_sub // /#.
by congr.
qed.



lemma ceil_3_2 : ceil (3%r / 2%r) = 2.
proof.
have ?: 1 < ceil (3%r / 2%r) by smt(@Real).
have ?: ceil (3%r / 2%r) <= 2 by smt(@Real).
smt().
qed.
