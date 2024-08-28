pragma Goals : printall.

require import AllCore List.
from Jasmin require import JModel.

require import Types Address Notation Primitives Wots.
require import XMSS_IMPL.

require import Array32 Array64 Array2144.

require import BitEncoding.
(*---*) import BitChunking.

(*---*) import NBytes.

(*****) import StdBigop.Bigint.

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


(*** Lemmas about signature ***)

lemma size_enc_wots_signature (x : W8.t Array2144.t) : size (EncodeWotsSignature x) = 67 (* 67 = len *)
    by rewrite /EncodeWotsSignature size_chunk 1:/# size_to_list //.

lemma ssize_enc_wots_signature (x : W8.t Array2144.t) : 
    forall (t : W8.t list), t \in (EncodeWotsSignature x) => size t = 32 by smt(@BitChunking).

lemma size_flatten_enc_wots_signature (x : W8.t Array2144.t) : size (flatten (EncodeWotsSignature x)) = 2144. (* 2144 = len . n *)
proof.
rewrite size_flatten sumzE BIA.big_map /(\o) //=.
rewrite -(StdBigop.Bigint.BIA.eq_big_seq (fun _ => 32)) /=; first by smt(ssize_enc_wots_signature).
rewrite big_constz count_predT.
have ->: size (EncodeWotsSignature x) = 67 by apply (size_enc_wots_signature).
smt(). 
qed.

(* aux *)
lemma enc_dec_wots_signature_r (x : W8.t Array2144.t) (y : wots_signature) :
    y = EncodeWotsSignature x => x = DecodeWotsSignature y.
proof.
move => Hy.
have H0 : size y = 67. by rewrite Hy; apply size_enc_wots_signature.
have H1 : forall (t : W8.t list), t \in y => size t = 32 by rewrite Hy; apply ssize_enc_wots_signature. 
rewrite /DecodeWotsSignature Hy /EncodeWotsSignature.
apply tP.
move => i Hi.
rewrite get_of_list; 1:assumption.
rewrite chunkK; 1,2:smt(size_to_list).
rewrite get_to_list //. 
qed.

(* aux *)
lemma enc_dec_wots_signature_l (x : W8.t Array2144.t) (y : wots_signature) :
    size y = 67 => 
     (forall (t : W8.t list), t \in y => size t = 32) =>
    x = DecodeWotsSignature y => y = EncodeWotsSignature x.
proof.
move => H0 H1 Hx.
rewrite /EncodeWotsSignature Hx /DecodeWotsSignature.
rewrite of_listK.
  + rewrite size_flatten sumzE BIA.big_map /(\o) //= -(StdBigop.Bigint.BIA.eq_big_seq (fun _ => 32)) /= 1:/# big_constz count_predT H0 /#.
rewrite flattenK /#.
qed.

lemma enc_dec_wots_signature (x : W8.t Array2144.t) (y : wots_signature) : 
    size y = 67 => 
      (forall (t : W8.t list), t \in y => size t = 32) => 
        x = DecodeWotsSignature y <=> y = EncodeWotsSignature x
          by move => ??; split; [ apply enc_dec_wots_signature_l => /# | apply enc_dec_wots_signature_r] .

(*** Lemmas about pk ***)

lemma size_enc_wots_pk (x : W8.t Array2144.t) : size (EncodeWotsPk x) = 67 (* 67 = len *)
    by rewrite /EncodeWotsPk size_chunk 1:/# size_to_list //.

lemma ssize_enc_wots_pk (x : W8.t Array2144.t) : 
    forall (t : W8.t list), t \in (EncodeWotsPk x) => size t = 32 by smt(@BitChunking).

lemma size_flatten_enc_wots_pk (x : W8.t Array2144.t) : size (flatten (EncodeWotsPk x)) = 2144. (* 2144 = len . n *)
proof.
rewrite size_flatten sumzE BIA.big_map /(\o) //=.
rewrite -(StdBigop.Bigint.BIA.eq_big_seq (fun _ => 32)) /=; first by smt(ssize_enc_wots_pk).
rewrite big_constz count_predT.
have ->: size (EncodeWotsPk x) = 67 by apply (size_enc_wots_pk).
smt(). 
qed.

(* aux *)
lemma enc_dec_wots_pk_r (x : W8.t Array2144.t) (y : wots_pk) :
    y = EncodeWotsPk x => x = DecodeWotsPk y.
proof.
move => Hy.
have H0 : size y = 67. by rewrite Hy; apply size_enc_wots_pk.
have H1 : forall (t : W8.t list), t \in y => size t = 32 by rewrite Hy; apply ssize_enc_wots_pk. 
rewrite /DecodeWotsPk Hy /EncodeWotsPk.
apply tP.
move => i Hi.
rewrite get_of_list; 1:assumption.
rewrite chunkK; 1,2:smt(size_to_list).
rewrite get_to_list //. 
qed.

(* aux *)
lemma enc_dec_wots_pk_l (x : W8.t Array2144.t) (y : wots_pk) :
    size y = 67 => 
     (forall (t : W8.t list), t \in y => size t = 32) =>
    x = DecodeWotsPk y => y = EncodeWotsPk x.
proof.
move => H0 H1 Hx.
rewrite /EncodeWotsPk Hx /DecodeWotsPk.
rewrite of_listK.
  + rewrite size_flatten sumzE BIA.big_map /(\o) //= -(StdBigop.Bigint.BIA.eq_big_seq (fun _ => 32)) /= 1:/# big_constz count_predT H0 /#.
rewrite flattenK /#.
qed.

lemma enc_dec_wots_pk (x : W8.t Array2144.t) (y : wots_pk) : 
    size y = 67 => 
      (forall (t : W8.t list), t \in y => size t = 32) => 
        x = DecodeWotsPk y <=> y = EncodeWotsPk x
          by move => ??; split; [ apply enc_dec_wots_pk_l => /# | apply enc_dec_wots_pk_r] .

(*** Lemmas about sk ***)

lemma size_enc_wots_sk (x : W8.t Array2144.t) : size (EncodeWotsSk x) = 67 (* 67 = len *)
    by rewrite /EncodeWotsSk size_chunk 1:/# size_to_list //.

lemma ssize_enc_wots_sk (x : W8.t Array2144.t) : 
    forall (t : W8.t list), t \in (EncodeWotsSk x) => size t = 32 by smt(@BitChunking).

lemma size_flatten_enc_wots_sk (x : W8.t Array2144.t) : size (flatten (EncodeWotsSk x)) = 2144. (* 2144 = len . n *)
proof.
rewrite size_flatten sumzE BIA.big_map /(\o) //=.
rewrite -(StdBigop.Bigint.BIA.eq_big_seq (fun _ => 32)) /=; first by smt(ssize_enc_wots_sk).
rewrite big_constz count_predT.
have ->: size (EncodeWotsSk x) = 67 by apply (size_enc_wots_sk).
smt(). 
qed.

(* aux *)
lemma enc_dec_wots_sk_r (x : W8.t Array2144.t) (y : wots_sk) :
    y = EncodeWotsSk x => x = DecodeWotsSk y.
proof.
move => Hy.
have H0 : size y = 67. by rewrite Hy; apply size_enc_wots_sk.
have H1 : forall (t : W8.t list), t \in y => size t = 32 by rewrite Hy; apply ssize_enc_wots_sk. 
rewrite /DecodeWotsSk Hy /EncodeWotsSk.
apply tP.
move => i Hi.
rewrite get_of_list; 1:assumption.
rewrite chunkK; 1,2:smt(size_to_list).
rewrite get_to_list //. 
qed.

(* aux *)
lemma enc_dec_wots_sk_l (x : W8.t Array2144.t) (y : wots_sk) :
    size y = 67 => 
     (forall (t : W8.t list), t \in y => size t = 32) =>
    x = DecodeWotsSk y => y = EncodeWotsSk x.
proof.
move => H0 H1 Hx.
rewrite /EncodeWotsSk Hx /DecodeWotsSk.
rewrite of_listK.
  + rewrite size_flatten sumzE BIA.big_map /(\o) //= -(StdBigop.Bigint.BIA.eq_big_seq (fun _ => 32)) /= 1:/# big_constz count_predT H0 /#.
rewrite flattenK /#.
qed.

lemma enc_dec_wots_sk (x : W8.t Array2144.t) (y : wots_sk) : 
    size y = 67 => 
      (forall (t : W8.t list), t \in y => size t = 32) => 
        x = DecodeWotsSk y <=> y = EncodeWotsSk x
          by move => ??; split; [ apply enc_dec_wots_sk_l => /# | apply enc_dec_wots_sk_r] .


(*-------------------------------------------------------------------------------------------------*)

op sig_from_ptr_array (mem : global_mem_t) (ptr : W64.t) : W8.t Array2144.t =     
  Array2144.init (fun (i : int) => loadW8 mem (to_uint ptr + i)).

op sig_from_ptr_list (mem : global_mem_t) (ptr : W64.t) : W8.t list =     
  mkseq (fun (i : int) => loadW8 mem (to_uint ptr + i)) 2144.

(**************************************************************************************************)
(*******************                        XMSS                                *******************)
(**************************************************************************************************)

