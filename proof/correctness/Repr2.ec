pragma Goals : printall.

require import AllCore List IntDiv.

from Jasmin require import JModel.

(*****) import StdBigop.Bigint.

require import BitEncoding.
(*---*) import BitChunking.

require import Params Types XMSS_MT_Types WOTS.
require import Utils2.

require import Array64 Array2144.

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

op EncodeWotsSignature (s : W8.t Array2144.t) : wots_signature = 
  LenNBytes.insubd (map NBytes.insubd (chunk 32 (to_list s))). 

op EncodeWotsSignatureList (s : W8.t list) : wots_signature = 
  LenNBytes.insubd (map NBytes.insubd (chunk 32 s)). 

op EncodeWotsPk (pk : W8.t Array2144.t) : wots_pk = 
  LenNBytes.insubd (map NBytes.insubd (chunk 32 (to_list pk))). 

(** -------------------------------------------------------------------------------------------- **)

(* aux *)
lemma enc_dec_wots_pk_r (x : W8.t Array2144.t) (y : wots_pk) :
    len = 67 /\ n = 32 =>
    y = EncodeWotsPk x => x = DecodeWotsPk y.
proof.
move => [#] len_val n_val H.
rewrite /DecodeWotsPk H /EncodeWotsPk.
rewrite tP => i?.
rewrite get_of_list; 1:assumption.
rewrite /nbytes_flatten (nth_flatten witness 32).
  + pose P := (fun (s : W8.t list) => size s = 32).
    pose L := (map NBytes.val (val (insubd (map NBytes.insubd (chunk 32 (to_list x)))))).
    rewrite -(all_nthP P L witness) /L /P size_map valP.
    rewrite insubdK; [ rewrite /P size_map size_chunk // size_to_list len_val //= |] => j?.  
    by rewrite (nth_map witness) 1:#smt:(size_map size_chunk size_to_list) valP n_val.         
rewrite (nth_map witness).
  + rewrite valP /#.
rewrite insubdK.
  + rewrite /P size_map size_chunk // size_to_list len_val //=.
rewrite (nth_map witness).
  + rewrite size_chunk // size_to_list /#. 
rewrite insubdK. 
  + rewrite /P /chunk nth_mkseq; [rewrite size_to_list /# |] => />. 
    rewrite size_take //= size_drop 1:/# size_to_list /#. 
rewrite /chunk nth_mkseq 1:#smt:(size_to_list) => />.
rewrite nth_take // 1:/# nth_drop 1,2:/# get_to_list /#. 
qed.

(* aux *)
lemma enc_dec_wots_pk_l (x : W8.t Array2144.t) (y : wots_pk) :
    len = 67 /\ n = 32 =>
    x = DecodeWotsPk y => y = EncodeWotsPk x.
proof.
move => [#] len_val n_val H. 
rewrite /EncodeWotsPk H /DecodeWotsPk.  
rewrite -len_nbytes_eq. 
apply (eq_from_nth witness).
  + rewrite valP insubdK; [rewrite /P size_map size_chunk // size_to_list len_val //= |].  
    rewrite size_map size_chunk // size_to_list len_val //=. 
rewrite valP len_val => j?. 
rewrite insubdK. 
  + rewrite /P size_map size_chunk // size_to_list len_val //=.
rewrite (nth_map witness). 
  + rewrite size_chunk // size_to_list /#.
rewrite /chunk nth_mkseq; [rewrite size_to_list //= |] => />. 
rewrite -nbytes_eq insubdK. 
  + rewrite /P size_take // size_drop 1:/# size_to_list n_val /#. 
apply (eq_from_nth witness).
  + rewrite valP size_take // size_drop 1:/# size_to_list n_val /#.
rewrite valP n_val => i?. 
rewrite nth_take // 1:/# nth_drop 1,2:/# get_to_list. 
rewrite get_of_list 1:/# /nbytes_flatten (nth_flatten witness 32). 
  + pose P := (fun (s : W8.t list) => size s = 32).
    pose L := (map NBytes.val (val y)).
    rewrite -(all_nthP P L witness) /L /P size_map valP len_val => ??.
    rewrite (nth_map witness); [by rewrite valP len_val |].
    rewrite valP n_val //. 
rewrite (nth_map witness) => [| /#].
rewrite valP len_val /#. 
qed.

lemma enc_dec_wots_pk (x : W8.t Array2144.t) (y : wots_pk) :
    len = 67 /\ n = 32 =>
    x = DecodeWotsPk y <=> y = EncodeWotsPk x.
proof.
move => [#] ??. 
split; [apply enc_dec_wots_pk_l | apply enc_dec_wots_pk_r] => /#.
qed.

lemma enc_comp_dec_pk (x : W8.t Array2144.t) :
    len = 67 /\ n = 32 =>
    x = DecodeWotsPk (EncodeWotsPk x).
proof.
move => [#] len_val n_val.
rewrite /DecodeWotsPk /EncodeWotsPk. 
rewrite tP => j?. 
rewrite get_of_list // insubdK. 
  + rewrite /P size_map size_chunk // size_to_list len_val //=.
rewrite /nbytes_flatten (nth_flatten witness 32). 
  + pose P := (fun (s : W8.t list) => size s = 32).
    pose L := (map NBytes.val (map NBytes.insubd (chunk 32 (to_list x)))).
    rewrite -(all_nthP P L witness) /L /P !size_map !size_iota (: max 0 (max 0 2144 %/ 32) = 67) 1:/# => i?.  
    rewrite (nth_map witness); [rewrite size_map size_chunk // size_to_list //= |].
    by rewrite valP n_val. 
rewrite (nth_map witness).
  + rewrite size_map size_chunk // size_to_list //= /#.
rewrite (nth_map witness).
  + rewrite size_chunk // size_to_list //= /#.
rewrite insubdK.
  + rewrite /P /chunk nth_mkseq 1:#smt:(size_to_list) => />.
    rewrite size_take // size_drop 1:/# size_to_list n_val /#. 
rewrite /chunk nth_mkseq 1:#smt:(size_to_list) => />.
rewrite nth_take // 1:/# nth_drop 1,2:/# get_to_list /#.
qed.

(** -------------------------------------------------------------------------------------------- **)

lemma wots_sk_size (sk : wots_sk) : size (val sk) = len by smt(LenNBytes.valP).

lemma wotS_sk_ssize (sk : wots_sk) :
    forall (t : nbytes), t \in val sk => size (val t) = n
      by smt(NBytes.valP).

(** -------------------------------------------------------------------------------------------- **)

require import LTree. (* AuthPath *)

op EncodePkNoOID (x : W8.t Array64.t) : xmss_pk = {| pk_oid      = witness;
                                                     pk_root     = NBytes.insubd (sub x 0 32); 
                                                     pk_pub_seed = NBytes.insubd (sub x 32 32);
                                                   |}. 


(* 
  signed message = msg || signature

  signature bytes = 2500
  msg = smlen - 2500
  
*)

op load_buf (mem : global_mem_t) (ptr : W64.t) (inlen : W64.t) =
  mkseq (fun (i : int) => mem.[to_uint ptr + i]) (to_uint inlen).

op concatMap  (f : 'a -> 'b list) (a : 'a list): 'b list = flatten (map f a).
op W32ofBytes (bytes : W8.t list) : W32.t = W32.bits2w (concatMap W8.w2bits bytes).
op sub_list (x : 'a list) (k len : int) : 'a list = mkseq (fun (i : int) => nth witness x (k + i)) len.

op EncodeAuthPath (x : W8.t list) : auth_path = AuthPath.insubd [NBytes.insubd (sub_list x 0 32)].

op EncodeReducedSignature (x : W8.t list) : reduced_signature =
  (EncodeWotsSignatureList (sub_list x 0 2144), EncodeAuthPath (sub_list x 2144 32)).

op EncodeSignedMessage (mem : global_mem_t) (sm_ptr smlen : W64.t) : sig_t =
  let mlen : W64.t  = smlen - W64.of_int 2500 in 
  let sig_ptr : W64.t = sm_ptr + mlen in 
  let signature : W8.t list =  load_buf mem sig_ptr (W64.of_int 2500) in
  {| sig_idx = W32ofBytes (sub_list signature 0 4);
     r       = NBytes.insubd (sub_list signature 4 32);
     r_sigs  = map EncodeReducedSignature (chunk 2176 (sub_list signature 36 (36 - 2500)));
  |}.
