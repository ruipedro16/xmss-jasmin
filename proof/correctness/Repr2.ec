pragma Goals : printall.

require import AllCore List IntDiv.

from Jasmin require import JModel.

(*****) import StdBigop.Bigint.

require import BitEncoding.
(*---*) import BitChunking.

require import Params WOTS.
require import Utils2.

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

op EncodeWotsSignature (s : W8.t Array2144.t) : wots_signature = 
  LenNBytes.insubd (map NBytes.insubd (chunk 32 (to_list s))). 

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

require import Types XMSS_MT_Types.
require import Array64.

op EncodePkNoOID (x : W8.t Array64.t) : xmss_pk = {| pk_oid      = witness;
                                                     pk_root     = NBytes.insubd (sub x 0 32); 
                                                     pk_pub_seed = NBytes.insubd (sub x 32 32);
                                                   |}. 
                                             
