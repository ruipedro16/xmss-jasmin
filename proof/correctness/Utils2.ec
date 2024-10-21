pragma Goals : printall.

require import AllCore List RealExp IntDiv.
require import BitEncoding.
(*---*) import BitChunking.

from Jasmin require import JModel.

require import Params Address Hash LTree.

require import Correctness_Address. (* FIXME: This should not be imported here ==> move W32toBytes to Utils *)

require import Array8.

(*****) import StdBigop.Bigint.

(** -------------------------------------------------------------------------------------------- **)

(* from MLKEM proof *)

(* m and m' are memories that differ on the contents of addresses in the range [p; p+len[ *)
pred touches (m m' : global_mem_t) (p : address) (len : int) =
    forall (i : int), !(0 <= i < len) => m'.[p + i] = m.[p + i].

(* m and m' are memories that differ on the contents of addresses 
   in the range [p1; p1+len1[ and 
   in the range [p2; p2+len2[
*)
pred touches2 (m m' : global_mem_t) (p1 p2 : address) (len1 len2 : int) =
  forall (a : int), ! (p1 <= a < p1 + len1) =>  
                    ! (p2 <= a < p2 + len2) => 
                        m'.[a] = m.[a].

lemma touches_touches2 (m m' : global_mem_t) (p1 p2 : address) (len1 len2 : int) :
    touches m m' p1 len1 /\ touches m m' p2 len2 =>
       touches2 m m' p1 p2 len1 len2 by smt().

(*  m and m' are memories that differ on the contents of address p *)
pred mem_dif (m m' : global_mem_t) (p : int) = m.[p] <> m'.[p].

(** -------------------------------------------------------------------------------------------- **)

op concatMap  (f: 'a -> 'b list) (a: 'a list): 'b list = flatten (map f a).

op W32ofBytes (bytes : W8.t list) : W32.t = W32.bits2w (concatMap W8.w2bits bytes).
op W64ofBytes (bytes : W8.t list) : W64.t = W64.bits2w (concatMap W8.w2bits bytes). (* isto ja faz zero ext *)

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

lemma size_singleton ['a] (x : 'a) : size [x] = 1 by smt(@List).

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
