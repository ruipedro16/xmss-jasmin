pragma Goals : printall.

require import AllCore List RealExp IntDiv.

require import BitEncoding.
(*---*) import BitChunking.

from Jasmin require import JModel.

require import Params.

require import Array3.

(** -------------------------------------------------------------------------------------------- **)

lemma nbyte_list_val_eq (a : W8.t list) (b :nbytes) : 
    size a = n => NBytes.insubd a = b => val b = a by 
      smt(@NBytes).

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

lemma simplify_pow (a b : int) : 
    0 < a /\ 0 < b => 
      a%r ^ b%r = (a ^ b)%r.
proof.
move => [#] ??.
rewrite -RField.fromintXn 1:/# #smt:(@RealExp).
qed.

hint simplify simplify_pow. 

lemma log2_16 : log2 16%r = 4%r.
proof.
have ->: 16%r = 2%r ^ 4%r by simplify.
rewrite /log2 logK /#.
qed.

lemma ceil_3_2 : ceil (3%r / 2%r) = 2.
proof.
have ? : 1 < ceil (3%r / 2%r) by smt(@Real).
have ? : ceil (3%r / 2%r) <= 2 by smt(@Real).
smt().
qed.

(** -------------------------------------------------------------------------------------------- **)

lemma array3_map_bounds (y : W32.t Array3.t) :
    (forall (x : int), x \in map W32.to_uint (to_list y) => 0 <= x && x < w) =>
    (forall (k : int), 0 <= k < 3 => 0 <= to_uint y.[k] < w).
proof.
move => E.
have E0 : forall (k : int), 0 <= k < 3 => 0 <= nth witness (map W32.to_uint (to_list y)) k < w by smt(@List).
move => k?.
rewrite -get_to_list. 
rewrite -(nth_map witness witness W32.to_uint). 
  + by rewrite size_to_list. 
apply E0 => //=. 
qed.
