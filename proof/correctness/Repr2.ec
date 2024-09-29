pragma Goals : printall.

require import AllCore List IntDiv.

from Jasmin require import JModel.

(*****) import StdBigop.Bigint.

require import Params Types WOTS XMSS_Params XMSS_MT_Types.

require import Array64 Array68 Array132 Array136 Array2144.

require import BitEncoding.
(*---*) import BitChunking.

(* Encode : impl -> spec *)
(* Decode : spec -> impl *)

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
print w2bits. 
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

(** -------------------------------------------------------------------------------------------- **)

op DecodePk (x : xmss_pk) : W8.t Array68.t = 
  Array68.of_list witness (W32toBytes impl_oid ++ val x.`pk_root ++ val x.`pk_pub_seed).

op DecodePkNoOID (x : xmss_pk) : W8.t Array64.t = 
  Array64.of_list witness (val x.`pk_root ++ val x.`pk_pub_seed).

op DecodeSk (x : xmss_sk) : W8.t Array136.t = 
  Array136.of_list witness (W32toBytes impl_oid ++ W32toBytes x.`idx ++ val x.`sk_seed ++ 
                            val x.`sk_prf ++ val x.`sk_root ++ val x.`pub_seed_sk).

op DecodeSkNoOID (x : xmss_sk) : W8.t Array132.t = 
  Array132.of_list witness (W32toBytes x.`idx ++ val x.`sk_seed ++ val x.`sk_prf ++ val x.`sk_root ++ val  x.`pub_seed_sk).

