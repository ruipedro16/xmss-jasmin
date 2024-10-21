pragma Goals : printall.

require import AllCore List IntDiv.

from Jasmin require import JModel.

(*****) import StdBigop.Bigint.

require import Params Parameters Types WOTS XMSS_MT_Params LTree XMSS_MT_Types.

require import Array32 Array64 Array68 Array131 Array2144.

require import BitEncoding.
(*---*) import BitChunking.

require import Utils2.


(* Encode : impl -> spec *)
(* Decode : spec -> impl *)

(** -------------------------------------------------------------------------------------------- **)

op sub_list ['a] (x : 'a list) (k len : int) : 'a list = 
  mkseq (fun (i : int) => nth witness x (k + i)) len.

lemma size_sub_list (x : 'a list) (k len : int) :
    0 <= len =>
      size (sub_list x k len) = len.
proof.
move => ?.
rewrite /sub_list size_mkseq /#.
qed.


(** -------------------------------------------------------------------------------------------- **)

op W32toBytes (x : W32.t) : W8.t list = map W8.bits2w (chunk W8.size (W32.w2bits x)).

lemma size_W32toBytes (x : W32.t) :
    size (W32toBytes x) = 4
        by rewrite /W32toBytes size_map size_chunk // size_w2bits. 

lemma W32toBytes_zero_nth (i : int) :
    0 <= i < 4 => nth witness (W32toBytes W32.zero) i = W8.zero.
proof.
move => H.
rewrite /W32toBytes.
rewrite (nth_map witness).
  + by rewrite size_chunk.
have ->: w2bits W32.zero = nseq 32 false.
  + apply (eq_from_nth false); [ by rewrite size_w2bits size_nseq |].
    rewrite size_w2bits => j?.
    rewrite get_w2bits nth_nseq //=.
have ->: chunk 8 (nseq 32 false) = nseq 4 (nseq 8 false).
  + apply (eq_from_nth witness); [by rewrite size_chunk //= !size_nseq /# |].
    rewrite size_chunk //= size_nseq (: 32 %/ 8 = 4) 1:/# => j?.
    rewrite nth_nseq 1:/#.
    rewrite /chunk nth_mkseq; [by rewrite size_nseq (: 32 %/ 8 = 4) 1:/# |].
    auto => />. 
    apply (eq_from_nth witness).
      * rewrite size_take //= size_drop 1:/# !size_nseq. 
        rewrite (: (max 0 32) = 32) 1:/# (: max 0 (32 - 8 * j) = (32 - 8 *j)) 1:/# /#. 
    rewrite size_take //= size_drop 1:/# !size_nseq.      
    rewrite (: (max 0 32) = 32) 1:/# (: max 0 (32 - 8 * j) = (32 - 8 *j)) 1:/#.
    move => i0?.
    rewrite nth_nseq 1:/# nth_take //= 1:/# nth_drop 1,2:/# nth_nseq 1:/# //.
rewrite nth_nseq //.
rewrite /W8.zero.
congr. 
apply (eq_from_nth false).
  + rewrite size_nseq /int2bs size_mkseq //=.
rewrite size_nseq (: max 0 8 = 8) 1:/# => j?.  
rewrite nth_nseq //= /int2bs nth_mkseq //=.
qed.

(** -------------------------------------------------------------------------------------------- **)

(* W8 list w/32 elements loaded from memory *)
op load_mem_w8_list32 (mem : global_mem_t) (ptr : W64.t) : W8.t list =
    mkseq (fun (i : int) => loadW8 mem (to_uint ptr + i)) 32.

lemma size_load_mem_w8_list32  (mem : global_mem_t) (ptr : W64.t) : 
    size (load_mem_w8_list32 mem ptr) = 32.
proof.
by rewrite /load_mem_w8_list32 size_mkseq.
qed.

op load_mem_w8_array32 (mem : global_mem_t) (ptr : W64.t) : W8.t Array32.t =
    Array32.init (fun (i : int) => loadW8 mem (to_uint ptr + i)).

lemma load_mem_list_array_32 (mem : global_mem_t) (ptr : W64.t) :
    load_mem_w8_list32 mem ptr = to_list (load_mem_w8_array32 mem ptr).
proof.
rewrite /load_mem_w8_list32 /load_mem_w8_array32.
apply (eq_from_nth witness) ; [ rewrite /to_list !size_mkseq //= | smt(@List @Array32) ].
qed.

(** -------------------------------------------------------------------------------------------- **)

op nbytes_flatten (x : nbytes list) : W8.t list =
  flatten (map (NBytes.val) x).

lemma size_nbytes_flatten_2 (x : nbytes list) :
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

op EncodeWotsSignature (s : W8.t Array2144.t) : wots_signature = 
  LenNBytes.insubd (map NBytes.insubd (chunk 32 (to_list s))). 

op EncodeWotsSignatureList (s : W8.t list) : wots_signature = 
  LenNBytes.insubd (map NBytes.insubd (chunk 32 s)). 

op DecodeWotsSignature_List (s : wots_signature) : W8.t list = nbytes_flatten (val s).

(** -------------------------------------------------------------------------------------------- **)

lemma wots_sk_ssize (sk : wots_sk) :
    forall (t : nbytes), t \in val sk => size (val t) = n
      by smt(NBytes.valP).

lemma wots_sig_size_flatten (s : wots_signature) :
    n = 32 /\ len = 67 =>
    size (flatten (map NBytes.val (val s))) = 2144.
proof.
move => [#] n_val len_val.
rewrite size_flatten sumzE BIA.big_map /(\o) //=. 
rewrite -(StdBigop.Bigint.BIA.eq_big_seq (fun _ => 32)) 1:#smt:(wots_sk_ssize @List @NBytes).
by rewrite big_constz count_predT size_map valP len_val.
qed.

(** -------------------------------------------------------------------------------------------- **)

op DecodePk (x : xmss_pk) : W8.t Array68.t = 
  Array68.of_list witness (W32toBytes impl_oid ++ val x.`pk_root ++ val x.`pk_pub_seed).

op DecodePkNoOID (x : xmss_pk) : W8.t Array64.t = 
  Array64.of_list witness (val x.`pk_root ++ val x.`pk_pub_seed).

op EncodePk (x : W8.t Array68.t) : xmss_pk = {| pk_oid      = W32ofBytes (sub x 0 4);
                                                pk_root     = NBytes.insubd (sub x 4 32); 
                                                pk_pub_seed = NBytes.insubd (sub x 36 32); 
                                              |}.

op EncodePkNoOID (x : W8.t Array64.t) : xmss_pk = {| pk_oid      = witness;
                                                     pk_root     = NBytes.insubd (sub x 0 32); 
                                                     pk_pub_seed = NBytes.insubd (sub x 32 32);
                                                   |}. 

op DecodeSk (x : xmss_sk) : W8.t Array131.t = 
  Array131.of_list witness (W32toBytes impl_oid ++ W32toBytes x.`idx ++ val x.`sk_seed ++ 
                            val x.`sk_prf ++ val x.`sk_root ++ val x.`pub_seed_sk).

op DecodeSkNoOID (x : xmss_sk) : W8.t Array131.t = 
  Array131.of_list witness (W32toBytes x.`idx ++ val x.`sk_seed ++ val x.`sk_prf ++ 
                            val x.`sk_root ++ val  x.`pub_seed_sk).

(** -------------------------------------------------------------------------------------------- **)

op EncodeAuthPath (x : W8.t list) : auth_path = 
  AuthPath.insubd (map NBytes.insubd (chunk n x)).

op DecodeAuthPath_List (ap : auth_path) : W8.t list = nbytes_flatten (val ap).

op EncodeReducedSignature (x : W8.t list) :  wots_signature * auth_path =
  (EncodeWotsSignatureList (sub_list x 0 2144), EncodeAuthPath (sub_list x 2144 32)).



(* sm = m || sig 
   we use mlen to skip the m part

   we receive a ptr to the signed message (= m || sig) and skip the m part
*)
op load_signature_mem (mem : global_mem_t) (sm_ptr mlen : W64.t) : W8.t list = 
  mkseq (fun (i : int) => loadW8 mem (to_uint (sm_ptr + mlen) + i)) XMSS_SIG_BYTES.

op EncodeSignature (sig_bytes : W8.t list) : sig_t =
  {| sig_idx  = W32ofBytes (sub_list sig_bytes 0 3);
     r        = NBytes.insubd (sub_list sig_bytes 3 32);
     r_sigs   = map EncodeReducedSignature (chunk 2176 (sub_list sig_bytes 36 (36 - 2500)));
  |}.
