pragma Goals : printall.

require import AllCore List IntDiv.

from Jasmin require import JModel.

(*****) import StdBigop.Bigint.

require import Params Parameters Types BaseW Hash WOTS XMSS_MT_Params LTree XMSS_MT_Types.

require import Array32 Array64 Array68 Array131 Array2144.

require import BitEncoding.
(*---*) import BitChunking.

require import Utils2.


(* Encode : impl -> spec *)
(* Decode : spec -> impl *)

(** -------------------------------------------------------------------------------------------- **)

op load_buf (mem : global_mem_t) (ptr : W64.t) (len : int) : W8.t list =
  mkseq (fun i => loadW8 mem (to_uint ptr + i)) len.

lemma size_load_buf (mem : global_mem_t) (ptr : W64.t) (len : int) :
    0 <= len =>
    size (load_buf mem ptr len) = len.
proof.
move => ?; rewrite /load_buf size_mkseq /#.
qed.

lemma nth_load_buf (mem : global_mem_t) (ptr : W64.t) (len i : int) :
    0 <= i < len =>
    nth witness (load_buf mem ptr len) i = mem.[to_uint ptr + i].
proof.
move => ?.
by rewrite nth_mkseq //=.
qed.

lemma load_buf_E (mem : global_mem_t) (ptr1 ptr2 : W64.t) (len : int):
    0 <= len =>
    load_buf mem ptr1 len = load_buf mem ptr2 len =>
    forall (k : int), 0 <= k < len => loadW8 mem (to_uint ptr1 + k) = loadW8 mem (to_uint ptr2 + k).
proof.
rewrite /load_buf => H0 H1.
move => k?.
have ->: loadW8 mem (to_uint ptr1 + k) = nth witness (mkseq (fun (i : int) => loadW8 mem (to_uint ptr1 + i)) len) k by rewrite /loadW8 nth_mkseq.
rewrite H1.
by rewrite /loadW8 nth_mkseq.
qed.

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

lemma nth_sub_list ['a] (x : 'a list) (k len : int) (i : int) :
    0 <= i < len =>
    nth witness (sub_list x k len) i = nth witness x (k + i).
proof.
move => ?.
rewrite /sub_list nth_mkseq //=.
qed.


op sub_mem_ptr (mem : global_mem_t) (ptr len : int) : W8.t list =
  mkseq (fun (i : int) => loadW8 mem (ptr + i)) len.
 
lemma size_sub_mem_ptr (mem : global_mem_t) (ptr len : int) :
    0 <= len =>
    size (sub_mem_ptr mem ptr len) = len.
proof.
move => ?.
rewrite /sub_mem_ptr.
rewrite size_mkseq /#.
qed.

(** -------------------------------------------------------------------------------------------- **)

lemma size_toByte_32 (x : W32.t) (i : int) : 
    0 <= i => 
    size (toByte x i) = i.
proof.
move => ?.
rewrite /toByte size_rev size_mkseq /#.
qed.

lemma size_toByte_64 (x : W64.t) (i : int) : 
    0 <= i => 
    size (toByte_64 x i) = i.
proof.
move => ?.
rewrite /toByte_64.
rewrite size_rev size_mkseq /#.
qed.

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

(* TMP: MOVE THIS TO THE RIGHT PLACE LATER *)
op BitsToBytes (bits : bool list) : W8.t list = map W8.bits2w (chunk W8.size bits).

lemma W32toBytes_Eq (x : W32.t) :
    W32toBytes x = 
    (mkseq (fun i => nth W8.zero (BitsToBytes (W32.w2bits x)) i) 4).
proof.
rewrite /W32toBytes.
apply (eq_from_nth witness); first by rewrite size_map size_chunk // size_w2bits size_mkseq /#.
rewrite size_map size_chunk // size_w2bits /= => j?.
rewrite nth_mkseq 1:/#.
rewrite /BitsToBytes.
rewrite (nth_map witness).
  + by rewrite size_chunk // size_w2bits.
rewrite wordP => jw?.
rewrite bits2wE initiE // /= /chunk nth_mkseq /= 1:/#.
rewrite nth_take // 1:/# nth_drop 1,2:/#.
rewrite (nth_map witness).
  +rewrite size_mkseq /#.
rewrite bits2wE initiE // /= /chunk nth_mkseq /= 1:/#.
rewrite nth_take // 1:/# nth_drop 1,2:/#.
by rewrite /w2bits nth_mkseq 1:/# /=.
qed.
   

(** -------------------------------------------------------------------------------------------- **)

op nbytes_flatten (x : nbytes list) : W8.t list =
  flatten (map (NBytes.val) x).

lemma nth_nbytes_flatten (x : nbytes list, i : int):
    0 <= i %/ n < size x =>
    nth witness (nbytes_flatten x) i = nth witness (val (nth witness x (i %/ n))) (i %% n).
move => H.
rewrite /nbytes_flatten (nth_flatten witness n).
    - pose P := (fun (s0 : W8.t list) => size s0 = n).
      pose L := (map NBytes.val x).
      rewrite -(all_nthP P L witness) /P /L size_map => j?. 
      by rewrite (nth_map witness) // valP.
by rewrite (nth_map witness).
qed.

(** -------------------------------------------------------------------------------------------- **)

op DecodeWotsSk (sk : wots_sk) : W8.t Array2144.t = 
  Array2144.of_list witness (nbytes_flatten (val sk)).

op DecodeWotsPk (pk : wots_pk) : W8.t Array2144.t = 
  Array2144.of_list witness (nbytes_flatten (val pk)).

op EncodeWotsPk (pk : W8.t Array2144.t) : wots_pk = 
  LenNBytes.insubd (map NBytes.insubd (chunk n (to_list pk))).

op EncodeWotsSignature (s : W8.t Array2144.t) : wots_signature = 
  LenNBytes.insubd (map NBytes.insubd (chunk 32 (to_list s))). 

op EncodeWotsSignatureList (s : W8.t list) : wots_signature = 
  LenNBytes.insubd (map NBytes.insubd (chunk 32 s)). 

lemma encodewotssig_list_array (s : W8.t Array2144.t) :
    EncodeWotsSignature s = EncodeWotsSignatureList (to_list s).
proof.
rewrite /EncodeWotsSignature /EncodeWotsSignatureList.
by congr.
qed.

op DecodeWotsSignature_List (s : wots_signature) : W8.t list = nbytes_flatten (val s).

lemma size_DecodeWotsSignature_List (x : wots_signature) :
    size (DecodeWotsSignature_List x) = n * len.
proof.
by rewrite /DecodeWotsSignature_List size_nbytes_flatten valP.
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

op EncodeIdx (idx : W32.t) : W8.t list = 
  take XMSS_INDEX_BYTES (W32toBytes idx).

lemma size_EncodeIdx (x : W32.t) : 
    size (EncodeIdx x) = XMSS_INDEX_BYTES by rewrite /EncodeIdx size_take 1:/# size_W32toBytes /#.

op DecodeSkNoOID (x : xmss_sk) : W8.t Array131.t = 
  Array131.of_list witness (
          EncodeIdx x.`idx ++ 
          val x.`sk_seed ++ 
          val x.`sk_prf ++ 
          val x.`sk_root ++ 
          val  x.`pub_seed_sk
  ).

(** -------------------------------------------------------------------------------------------- **)

lemma enc_dec_wots_pk (pk : wots_pk) :
    n = XMSS_N /\ len = XMSS_WOTS_LEN =>
    pk = EncodeWotsPk (DecodeWotsPk pk).
proof.
rewrite /XMSS_N /XMSS_WOTS_LEN => [#] n_val len_val.
rewrite /EncodeWotsPk /DecodeWotsPk.
apply len_n_bytes_eq.
apply (eq_from_nth witness); first by rewrite !valP.
rewrite valP => j?.
rewrite insubdK.
  + by rewrite /P size_map size_chunk 1:/# size_to_list n_val len_val.
rewrite (nth_map witness).
  + rewrite size_chunk 1:/# size_to_list n_val /#.
rewrite /chunk nth_mkseq.
  + rewrite size_to_list n_val /#.
apply nbytes_eq.
rewrite insubdK.
  + rewrite /P size_take 1:/# size_drop 1:/# size_to_list /#.
simplify.
apply (eq_from_nth witness); first by rewrite size_take 1:/# size_drop 1:/# size_to_list valP /#.
rewrite valP n_val => i?.
rewrite nth_take // 1:/# nth_drop 1,2:/# get_to_list get_of_list 1:/#.
rewrite /nbytes_flatten (nth_flatten witness n).
  + pose P := (fun (s : W8.t list) => size s = n).
    pose L := (map NBytes.val (val pk)).
    rewrite -(all_nthP P L witness) /P /L size_map valP n_val => l Hl. 
    rewrite (nth_map witness).
       - by rewrite valP.
    by rewrite valP.
rewrite (nth_map witness).
  + rewrite valP /#.
smt().
qed.

(** -------------------------------------------------------------------------------------------- **)


op EncodeAuthPath (x : W8.t list) : auth_path = 
  AuthPath.insubd (map NBytes.insubd (chunk n x)).

op DecodeAuthPath_List (ap : auth_path) : W8.t list = nbytes_flatten (val ap).

lemma size_DecodeAuthPath_List (x : auth_path) :
    size (DecodeAuthPath_List x) = n * (h %/ d).
proof.
by rewrite /DecodeAuthPath_List size_nbytes_flatten valP.
qed.

op EncodeReducedSignature (x : W8.t list) :  wots_signature * auth_path =
  (EncodeWotsSignatureList (sub_list x 0 2144), EncodeAuthPath (sub_list x 2144 320)).


(* sm = m || sig 
   we use mlen to skip the m part

   we receive a ptr to the signed message (= m || sig) and skip the m part
*)
op load_signature_mem (mem : global_mem_t) (sm_ptr mlen : W64.t) : W8.t list = 
  mkseq (fun (i : int) => loadW8 mem (to_uint (sm_ptr + mlen) + i)) XMSS_SIG_BYTES.

op EncodeSignature (sig_bytes : W8.t list) : sig_t =
  {| sig_idx  = W32ofBytes (sub_list sig_bytes 0 XMSS_INDEX_BYTES);
     r        = NBytes.insubd (sub_list sig_bytes XMSS_INDEX_BYTES XMSS_N);
     r_sigs   = map EncodeReducedSignature (chunk 2176 (sub_list sig_bytes 36 (36 - 2500)));
  |}.

lemma sig_eq (s1 s2 : sig_t) :
    s1.`sig_idx = s2.`sig_idx /\
    s1.`r       = s2.`r       /\
    s1.`r_sigs  = s2.`r_sigs => 
    s1 = s2 by smt(). 

lemma encode_signature_i (x y : W8.t list) : 
    x = y => 
    EncodeSignature x = EncodeSignature y.
proof.
move => ->; reflexivity.
qed.


lemma w2bits_eq_w32_w64 (w0 : W32.t) (w1 : W64.t) :
    to_uint w0 = to_uint w1 =>
    forall (k : int), 0 <= k < 32 => 
     nth witness (w2bits w0) k = nth witness (w2bits w1) k.
proof.
rewrite !to_uintE => ?.
admit.
qed.

lemma toByte_eq (w0 : W32.t) (w1 : W64.t):
    to_uint w0 = to_uint w1 =>
    EncodeIdx w0 = toByte_64 w1 XMSS_INDEX_BYTES.
proof.
move => ?.
apply (eq_from_nth witness).
  - rewrite size_EncodeIdx size_toByte_64 // /#.
rewrite size_EncodeIdx /XMSS_INDEX_BYTES => j?.
rewrite /EncodeIdx /toByte_64.
rewrite nth_take 1,2:/#.
rewrite /W32toBytes.
rewrite nth_rev.
  - rewrite size_mkseq /#.
rewrite nth_mkseq /=.
  - rewrite size_mkseq /#.
rewrite size_mkseq (: max 0 3 = 3) 1:/#.
rewrite (nth_map witness).
  - rewrite size_chunk /#.
rewrite bits2wE.
rewrite /BitsToBytes (nth_map witness).
  - rewrite size_iota /#.
rewrite (nth_map witness).
  - rewrite size_chunk /#.
rewrite bits2wE wordP => w?.
rewrite !initiE //= nth_take // 1:/# nth_drop 2:/#.
  - rewrite nth_iota /#.
rewrite !w2bitsE nth_iota 1:/#.
rewrite nth_mkseq 1:/# /=.
rewrite /chunk nth_mkseq.
  - rewrite size_mkseq 1:/#.
rewrite nth_take 1,2:/# nth_drop 1,2:/# nth_mkseq 1:/#.
admit. 
qed.
