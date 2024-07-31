pragma Goals : printall.

require import AllCore List.
from Jasmin require import JModel.

require import Address Notation Primitives Wots.
require import RandomBytes XMSS_IMPL.

require import Array32 Array64 Array2144.

require import BitEncoding.
(*---*) import BitChunking.

(*---*) import NBytes.

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
(*******************                        WOTS                                *******************)
(**************************************************************************************************)

(* Encode : impl -> spec *)
(* Decode : spec -> impl *)

op EncodeWotsMessage (m : W8.t Array32.t) : nbytes = to_list m.
op EncodeWotsMsgBaseW (m : W8.t Array64.t) : W8.t list = to_list m.
op EncodeWotsSignature (s : W8.t Array2144.t) : wots_signature = chunk 32 (to_list s). (* cada chunk tem nbytes /\ n = 32 *)
op EncodeWotsPk (pk : W8.t Array2144.t) : wots_pk = chunk 32 (to_list pk).
op EncodeWotsSk (sk : W8.t Array2144.t) : wots_sk = chunk 32 (to_list sk).

op DecodeWotsMessage (m : wots_message) : W8.t Array32.t = Array32.of_list witness m.
op DecodeWotsMsgBaseW (m : wots_message_base_w) : W8.t Array64.t = Array64.of_list witness m.
op DecodeWotsSignature (s : wots_signature) : W8.t Array2144.t = Array2144.of_list witness (flatten s).
op DecodeWotsPk (pk : wots_pk) : W8.t Array2144.t = Array2144.of_list witness (flatten pk).
op DecodeWotsSk (sk : wots_sk) : W8.t Array2144.t = Array2144.of_list witness (flatten sk).

(*-------------------------------------------------------------------------------------------------*)

op sig_from_ptr_array (mem : global_mem_t) (ptr : W64.t) : W8.t Array2144.t =     
  Array2144.init (fun (i : int) => loadW8 mem (to_uint ptr + i)).

op sig_from_ptr_list (mem : global_mem_t) (ptr : W64.t) : W8.t list =     
  mkseq (fun (i : int) => loadW8 mem (to_uint ptr + i)) 2144.

(**************************************************************************************************)
(*******************                        XNSS                                *******************)
(**************************************************************************************************)

