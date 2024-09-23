pragma Goals : printall.

require import AllCore List RealExp IntDiv.

require import BitEncoding.
(*---*) import BitChunking.

from Jasmin require import JModel.

require import Params.

require import Array3 Array64 Array2144.

(** -------------------------------------------------------------------------------------------- **)

lemma sub_ext (x : W8.t Array64.t) (y : W8.t Array2144.t) (i : int) :
    0 <= i < 2144 - 64 =>
      to_list x = sub y i 64 =>
       forall (k : int), 0 <= k < 64 => x.[k] = y.[i + k].
proof.
move => ?. 
admit.
qed.

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

lemma len_nbytes_eq:
  forall (s1 s2 : len_nbytes), val s1 = val s2 <=> s1 = s2
    by smt(@LenNBytes).
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

(** -------------------------------------------------------------------------------------------- **)

lemma truncate_1_and_63 :
    truncateu8 (W256.one `&` W256.of_int(63)) = W8.one
        by rewrite (: 63 = 2 ^ 6 - 1) 1:/# and_mod //=.

lemma shr_1 (x : W64.t) :
    to_uint (x `>>` W8.one) = to_uint x %/ 2
        by rewrite shr_div (: (to_uint W8.one %% 64) = 1) 1:#smt:(@W64) //=. 

lemma and_1_mod_2 (x : W64.t):
    x `&` W64.one <> W64.zero <=> to_uint x %% 2 = 1.
proof.
split; rewrite (: 1 = 2 ^ 1 - 1) 1:/# and_mod //=; [smt(foo) |].
move => H.
rewrite foo //= #smt:(@W64). 
qed.
