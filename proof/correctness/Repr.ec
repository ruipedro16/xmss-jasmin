pragma Goals : printall.

require import AllCore List.
from Jasmin require import JModel.

require import Types Address Notation Primitives Wots XMSS_MT_PRF.
require import Utils.
require import XMSS_IMPL.

require import Array32 Array64 Array68 Array132 Array136 Array320 Array2144.

require import BitEncoding.
(*---*) import BitChunking.

(*---*) import AuthPath.

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
rewrite -(StdBigop.Bigint.BIA.eq_big_seq (fun _ => 32)) /=; [smt(ssize_enc_wots_signature) |].
rewrite big_constz count_predT.
have ->: size (EncodeWotsSignature x) = 67 by apply (size_enc_wots_signature).
by simplify.
qed.

(* aux *)
lemma enc_dec_wots_signature_r (x : W8.t Array2144.t) (y : wots_signature) :
    y = EncodeWotsSignature x => x = DecodeWotsSignature y.
proof.
move => Hy.
have ?: size y = 67 by rewrite Hy; apply size_enc_wots_signature.
have ?: forall (t : W8.t list), t \in y => size t = 32 by rewrite Hy; apply ssize_enc_wots_signature. 
rewrite /DecodeWotsSignature Hy /EncodeWotsSignature.
apply tP.
move => ??.
rewrite get_of_list; 1:assumption.
rewrite chunkK;[ by [] | by rewrite size_to_list | by rewrite get_to_list ].
qed.

(* aux *)
lemma enc_dec_wots_signature_l (x : W8.t Array2144.t) (y : wots_signature) :
    size y = 67 => 
     (forall (t : W8.t list), t \in y => size t = 32) =>
    x = DecodeWotsSignature y => y = EncodeWotsSignature x.
proof.
move => H0 ? Hx.
rewrite /EncodeWotsSignature Hx /DecodeWotsSignature.
rewrite of_listK.
  + rewrite size_flatten sumzE BIA.big_map /(\o) //= -(StdBigop.Bigint.BIA.eq_big_seq (fun _ => 32)) /= 1:/# big_constz count_predT H0 /#.
rewrite flattenK; 1,3: by simplify. 
assumption.
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
rewrite -(StdBigop.Bigint.BIA.eq_big_seq (fun _ => 32)) /=; [ smt(ssize_enc_wots_pk) |].
rewrite big_constz count_predT.
have ->: size (EncodeWotsPk x) = 67 by apply (size_enc_wots_pk).
by simplify. 
qed.

(* aux *)
lemma enc_dec_wots_pk_r (x : W8.t Array2144.t) (y : wots_pk) :
    y = EncodeWotsPk x => x = DecodeWotsPk y.
proof.
move => Hy.
have ?: size y = 67 by rewrite Hy; apply size_enc_wots_pk.
have ?: forall (t : W8.t list), t \in y => size t = 32 by rewrite Hy; apply ssize_enc_wots_pk. 
rewrite /DecodeWotsPk Hy /EncodeWotsPk.
apply tP.
move => ??.
rewrite get_of_list; 1:assumption.
rewrite chunkK;[ by [] | by rewrite size_to_list | by rewrite get_to_list ].
qed. 

(* aux *)
lemma enc_dec_wots_pk_l (x : W8.t Array2144.t) (y : wots_pk) :
    size y = 67 => 
     (forall (t : W8.t list), t \in y => size t = 32) =>
    x = DecodeWotsPk y => y = EncodeWotsPk x.
proof.
move => H0 ? Hx.
rewrite /EncodeWotsPk Hx /DecodeWotsPk.
rewrite of_listK.
  + rewrite size_flatten sumzE BIA.big_map /(\o) //= -(StdBigop.Bigint.BIA.eq_big_seq (fun _ => 32)) /= 1:/# big_constz count_predT H0 /#.
rewrite flattenK; 1,3: by simplify.
assumption. 
qed.

lemma enc_dec_wots_pk (x : W8.t Array2144.t) (y : wots_pk) : 
    size y = 67 => 
      (forall (t : W8.t list), t \in y => size t = 32) => 
        x = DecodeWotsPk y <=> y = EncodeWotsPk x
          by move => ??; split; [ apply enc_dec_wots_pk_l | apply enc_dec_wots_pk_r] .

(*** Lemmas about sk ***)

lemma size_enc_wots_sk (x : W8.t Array2144.t) : size (EncodeWotsSk x) = 67 (* 67 = len *)
    by rewrite /EncodeWotsSk size_chunk 1:/# size_to_list //.

lemma ssize_enc_wots_sk (x : W8.t Array2144.t) : 
    forall (t : W8.t list), t \in (EncodeWotsSk x) => size t = 32 by smt(@BitChunking).

lemma size_flatten_enc_wots_sk (x : W8.t Array2144.t) : size (flatten (EncodeWotsSk x)) = 2144. (* 2144 = len . n *)
proof.
rewrite size_flatten sumzE BIA.big_map /(\o) //=.
rewrite -(StdBigop.Bigint.BIA.eq_big_seq (fun _ => 32)) /=; [ smt(ssize_enc_wots_sk) |].
rewrite big_constz count_predT.
have ->: size (EncodeWotsSk x) = 67 by apply (size_enc_wots_sk).
by simplify. 
qed.

(* aux *)
lemma enc_dec_wots_sk_r (x : W8.t Array2144.t) (y : wots_sk) :
    y = EncodeWotsSk x => x = DecodeWotsSk y.
proof.
move => Hy.
have ?: size y = 67 by rewrite Hy; apply size_enc_wots_sk.
have ?: forall (t : W8.t list), t \in y => size t = 32 by rewrite Hy; apply ssize_enc_wots_sk. 
rewrite /DecodeWotsSk Hy /EncodeWotsSk.
apply tP.
move => ??.
rewrite get_of_list; 1:assumption.
rewrite chunkK;[ by [] | by rewrite size_to_list | by rewrite get_to_list ].
qed.

(* aux *)
lemma enc_dec_wots_sk_l (x : W8.t Array2144.t) (y : wots_sk) :
    size y = 67 => 
     (forall (t : W8.t list), t \in y => size t = 32) =>
    x = DecodeWotsSk y => y = EncodeWotsSk x.
proof.
move => H0 ? Hx.
rewrite /EncodeWotsSk Hx /DecodeWotsSk.
rewrite of_listK.
  + rewrite size_flatten sumzE BIA.big_map /(\o) //= -(StdBigop.Bigint.BIA.eq_big_seq (fun _ => 32)) /= 1:/# big_constz count_predT H0 /#.
rewrite flattenK; 1,3: by simplify. 
assumption.
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

op EncodeAuthPath (x : W8.t Array320.t) : auth_path = chunk 32 (to_list x). 

(*
SK = OID || IDX || SK SEED || SK PRF || PUB SEED || ROOT (In the spec, the OID is ommited)

OID & IDX are 4 bytes each 
SK SEEDK SK PRF PUB SEED & ROOT are n bytes each, with n = 32

OID      | goes from index 0   to 3   (4  bytes) [0,   3]
IDX      | goes from index 4   to 7   (4  bytes) [4,   7]
SK SEED  | goes from index 8   to 39  (32 bytes) [8,   39]
SK PRF   | goes from index 40  to 71  (32 bytes) [40,  71]
PUB SEED | goes from index 72  to 103 (32 bytes) [72,  103]
ROOT     | goes from index 104 to 135 (32 bytes) [104, 134]

NOTE: PUB SEED & ROOT ARE SWITCHED
*)
op EncodeSk (x : W8.t Array136.t) : xmss_mt_sk = {| idx         = W32ofBytes (sub x 4 4);
                                                    sk_seed     = sub x 8 32; 
                                                    sk_prf      = sub x 40 32;
                                                    pub_seed_sk = sub x 104 32;
                                                    sk_root     = sub x 72 32 
                                                 |}.

op EncodeSkNoOID (x : W8.t Array132.t) : xmss_mt_sk = {| idx         = witness;
                                                         sk_seed     = sub x 0 32;
                                                         sk_prf      = sub x 32 32;
                                                         pub_seed_sk = sub x 96 32;
                                                         sk_root     = sub x 64 32;
                                                      |}. 
                                                        
(*
PK = OID || ROOT || PUB SEED (Both the spec and the impl have the oid)

OID is 4 bytes
ROOT & PUB SEED are both n bytes each, with n = 32

OID      | goes from index 0 to 3   (4  bytes) [0,  3]
PUB SEED | goes from index 4 to 35  (32 bytes) [4,  35] 
ROOT     | goes from index 36 to 67 (32 bytes) [36, 67]

*)
op EncodePk (x : W8.t Array68.t) : xmss_mt_pk = {| pk_oid      = W32ofBytes (sub x 0 4);
                                                   pk_root     = sub x 4 32; 
                                                   pk_pub_seed = sub x 36 32; 
                                                 |}.

op EncodePkNoOID (x : W8.t Array64.t) : xmss_mt_pk = {| pk_oid      = witness;
                                                        pk_root     = sub x 0 32; 
                                                        pk_pub_seed = sub x 32 32;
                                                     |}. 
                                             

op DecodeAuthPath (x : auth_path) : W8.t Array320.t = Array320.of_list witness (flatten x).

op DecodeSk (x : xmss_mt_sk) : W8.t Array136.t = 
  Array136.of_list witness (W32toBytes impl_oid ++ W32toBytes x.`idx ++ x.`sk_seed ++ 
                            x.`sk_prf ++  x.`sk_root ++ x.`pub_seed_sk).

op DecodeSkNoOID (x : xmss_mt_sk) : W8.t Array132.t = 
  Array132.of_list witness (W32toBytes x.`idx ++ x.`sk_seed ++ x.`sk_prf ++ x.`sk_root ++  x.`pub_seed_sk).

op DecodePk (x : xmss_mt_pk) : W8.t Array68.t = 
  Array68.of_list witness (W32toBytes impl_oid ++ x.`pk_root ++ x.`pk_pub_seed).

op DecodePkNoOID (x : xmss_mt_pk) : W8.t Array64.t = 
  Array64.of_list witness (x.`pk_root ++ x.`pk_pub_seed).

(* Compares an array of size 132 with the record type, ignoring the OID *)
pred skEqNoOID (x : W8.t Array132.t) (y : xmss_mt_sk) = x = DecodeSkNoOID y.

(*** Lemmas about authentication path ***)

lemma size_enc_authpath (x : W8.t Array320.t) :
    size (EncodeAuthPath x) = 10 by rewrite /EncodeAuthPath size_chunk // size_to_list //.

lemma ssize_enc_authpath (x : W8.t Array320.t) : 
    forall (t : W8.t list), t \in (EncodeAuthPath x) => size t = 32 by smt(@BitChunking). 

lemma size_flatten_enc_authpath (x : W8.t Array320.t) :
    size (flatten (EncodeAuthPath x)) = 320.
proof.
rewrite size_flatten sumzE BIA.big_map /(\o) //=.
rewrite -(StdBigop.Bigint.BIA.eq_big_seq (fun _ => 32)) /=; [smt(ssize_enc_authpath) |]. 
rewrite big_constz count_predT.
have ->: size (EncodeAuthPath x) = 10 by apply size_enc_authpath. 
by simplify. 
qed.

(*aux *)
lemma enc_dec_auth_path_r (x : W8.t Array320.t) (y : auth_path) : 
    y = EncodeAuthPath x => x = DecodeAuthPath y.    
proof.
move => Hy. 
have ?: size y = 10 by rewrite Hy; apply size_enc_authpath. 
have ?: forall (t : W8.t list), t \in y => size t = 32 by rewrite Hy; apply ssize_enc_authpath. 
rewrite /DecodeAuthPath Hy /EncodeAuthPath. 
rewrite tP. 
move => ??. 
rewrite get_of_list; 1:assumption.  
rewrite chunkK;[ by [] | by rewrite size_to_list | by rewrite get_to_list ].
qed.

(* aux *)
lemma enc_dec_auth_path_l (x : W8.t Array320.t) (y : auth_path) :
    size y = 10 =>
      (forall (t : W8.t list), t \in y => size t = 32) =>
        x = DecodeAuthPath y => y = EncodeAuthPath x.
proof.
move => H0 H1 Hx. 
rewrite /EncodeAuthPath Hx /DecodeAuthPath. 
rewrite of_listK; last first. 
  + rewrite flattenK; 1,3: by simplify. assumption. 
rewrite size_flatten sumzE BIA.big_map /(\o) //= 
       -(StdBigop.Bigint.BIA.eq_big_seq (fun _ => 32)) /= 1:/#
       big_constz count_predT H0 //=.
qed.

lemma enc_dec_auth_path (x : W8.t Array320.t) (y : auth_path) :
    size y = 10 =>
      (forall (t : W8.t list), t \in y => size t = 32) =>
        x = DecodeAuthPath y <=> y = EncodeAuthPath x
          by move => ??; split; [ apply enc_dec_auth_path_l | apply enc_dec_auth_path_r ].

(*** Lemmas about sk ***)

lemma enc_dec_sk_l (x : W8.t Array136.t) (y : xmss_mt_sk) :
    x = DecodeSk y => y = EncodeSk x.
proof.
rewrite /EncodeSk /DecodeSk.
admit.
qed.

lemma enc_dec_sk_r (x : W8.t Array136.t) (y : xmss_mt_sk) :
    size y.`sk_seed     = 32 /\
    size y.`sk_prf      = 32 /\
    size y.`pub_seed_sk = 32 =>
    y = EncodeSk x => x = DecodeSk y.
proof.
move => [#] H0 H1 H2 Hy.
rewrite /DecodeSk /EncodeSk. 
rewrite tP.
move => i Hi.
rewrite get_of_list; 1:assumption. 
rewrite !nth_cat !size_cat !size_W32toBytes H0 H1 H2 //=.
case (i < 104); last by smt(@List @Array136). 
move => ?; case (i < 72); last by smt(@List @Array136). 
move => ?; case (i < 40); last by smt(@List @Array136). 
move => ?; case (i < 8); last by smt(@List @Array136). 
move => ?; case (i < 4); move => H. 
  + admit.
  + admit.
qed.


lemma enc_dec_sk (x : W8.t Array136.t) (y : xmss_mt_sk) :
    size y.`sk_seed = 32 /\ 
    size y.`sk_prf = 32 /\ 
    size y.`pub_seed_sk = 32 =>
    x = DecodeSk y <=> y = EncodeSk x
      by move => ?; split; [apply enc_dec_sk_l | apply enc_dec_sk_r; assumption]. 

