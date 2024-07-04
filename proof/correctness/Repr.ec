pragma Goals : printall.

require import AllCore List.
from Jasmin require import JModel.

require import Address Wots XMSS_MT_PRF.
require import XMSS_IMPL XMSS_IMPL_PP.

require import Array32 Array2144.

(* 
    Operators to convert impl representation (i.e. arrays) to spec representation and
    predicates for equality 

    Enc :: Spec -> Impl
    Dec :: Impl -> Spec
    
    Dec . Enc = Id
*)

(**************************************************************************************************)
(*******************                        MEM                                 *******************)
(**************************************************************************************************)

(* W8 list w/32 elements loaded from memory *)
op load_mem_w8_list32 (mem : global_mem_t) (ptr : W64.t) : W8.t list =
    mkseq (fun (i : int) => loadW8 mem (to_uint ptr + i)) 32.

op load_mem_w8_array32 (mem : global_mem_t) (ptr : W64.t) : W8.t Array32.t =
    Array32.init (fun (i : int) => loadW8 mem (to_uint ptr + i)).

lemma load_mem_list_array_32 (mem : global_mem_t) (ptr : W64.t) :
    load_mem_w8_list32 mem ptr = to_list (load_mem_w8_array32 mem ptr).
proof.
rewrite /load_mem_w8_list32 /load_mem_w8_array32.
apply (eq_from_nth witness) ; [ rewrite /to_list !size_mkseq //= | smt(@List @Array32) ].
qed.


(**************************************************************************************************)
(*******************                        HASH                                *******************)
(**************************************************************************************************)


(**************************************************************************************************)
(*******************                        WOTS                                *******************)
(**************************************************************************************************)

op enc_wots_sk (sk : wots_sk) : W8.t Array2144.t =
    Array2144.of_list witness (flatten sk).


pred eq_wots_sk (sk_impl : W8.t Array2144.t) (sk_spec : wots_sk) = 
    flatten sk_spec = (to_list sk_impl).

op enc_wots_pk (pk : wots_pk) : W8.t Array2144.t =
    Array2144.of_list witness (flatten pk).


pred eq_wots_pk (pk_impl : W8.t Array2144.t) (pk_spec : wots_pk) = 
    flatten pk_spec = (to_list pk_impl).

(**************************************************************************************************)
(*******************                        XNSS                                *******************)
(**************************************************************************************************)

