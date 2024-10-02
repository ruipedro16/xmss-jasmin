pragma Goals : printall.

require import AllCore List RealExp IntDiv.
require import BitEncoding.
(*---*) import BitChunking.

from Jasmin require import JModel.

require import Params Address Hash.

require import Correctness_Address. (* FIXME: This should not be imported here ==> move W32toBytes to Utils *)

require import Array8.

(** -------------------------------------------------------------------------------------------- **)

(* from MLKEM proof *)
op touches (m m' : global_mem_t) (p : address) (len : int) =
    forall i, !(0 <= i < len) => m'.[p + i] = m.[p + i].

op touches2 (m m' : global_mem_t) (p1 : address) (len1 : int) (p2 : address) (len2 : int) : bool =
  forall (a : int), ! (p1 <=  a < p1+len1) =>  ! (p2 <=  a < p2+len2) => m'.[a] = m.[a].


(* 
  m1 and m2 are memories whose contect is equal except for the indices in the 
  ptr_dif list
 *)
pred mem_dif (m1 m2 : global_mem_t) (ptrs_dif : int list) = 
  forall (k : int), 0 <= k /\ ! (k \in ptrs_dif) => 
    m1.[k] = m2.[k].


(** -------------------------------------------------------------------------------------------- **)

op concatMap  (f: 'a -> 'b list) (a: 'a list): 'b list = flatten (map f a).
op W32ofBytes (bytes : W8.t list) : W32.t = W32.bits2w (concatMap W8.w2bits bytes).
op W64ofBytes (bytes : W8.t list) : W64.t = W64.bits2w (concatMap W8.w2bits bytes).


lemma W64_W32_of_bytes (t : W8.t list) :
    0 < size t <= 4 => 
       to_uint (W32ofBytes t) = to_uint (W64ofBytes t).
proof.
move => H.
admit.
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

