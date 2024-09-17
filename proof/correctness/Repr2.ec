pragma Goals : printall.

require import AllCore List.

from Jasmin require import JModel.

(*****) import StdBigop.Bigint.

require import Params WOTS.

require import Array2144.

(* Encode : impl -> spec *)
(* Decode : spec -> impl *)

op nbytes_flatten (x : nbytes list) : W8.t list =
  flatten (map (NBytes.val) x).

lemma size_nbytes_flatten (x : nbytes list) :
    size (nbytes_flatten x) = n * size x.
proof.
rewrite /nbytes_flatten size_flatten sumzE BIA.big_map /(\o) //=. 
rewrite -(StdBigop.Bigint.BIA.eq_big_seq (fun _ => n)) /=.
  + move => ?.  
    rewrite mapP #smt:(NBytes.valP).
rewrite big_constz count_predT size_map //=.
qed.

(** -------------------------------------------------------------------------------------------- **)

op DecodeWotsSk (sk : wots_sk) : W8.t Array2144.t = 
  Array2144.of_list witness (nbytes_flatten (val sk)).

op DecodeWotsPk (pk : wots_pk) : W8.t Array2144.t = 
  Array2144.of_list witness (nbytes_flatten (val pk)).

(** -------------------------------------------------------------------------------------------- **)

lemma wots_sk_size (sk : wots_sk) : size (val sk) = len by smt(LenNBytes.valP).

lemma wotS_sk_ssize (sk : wots_sk) :
    forall (t : nbytes), t \in val sk => size (val t) = n
      by smt(NBytes.valP).
