pragma Goals : printall.

require import AllCore List RealExp IntDiv Distr DList IntDiv.
from Jasmin require import JModel JArray.

require import Params Types Hash XMSS_MT_PRF XMSS_MT_Types XMSS_MT_Params.
require import XMSS_IMPL Parameters.

require import Repr2. 
require import Utils2.

require import Array3 Array8 Array32 Array64 Array68 Array96 Array131 Array352 Array2144 Array4963.
require import WArray32 WArray96 WArray131.

require import Correctness_Address Correctness_Bytes Correctness_Mem Correctness_Hash.
require import DistrUtils.

require import BitEncoding.
(*---*) import BitChunking.

require import StdBigop. 
(*---*) import Bigint.

lemma sign_invalid_idx :
    hoare [
      M(Syscall).__xmssmt_core_sign :
      2^XMSS_FULL_HEIGHT < to_uint (W64ofBytes (sub sk 0 3))
      ==> 
      res.`2 <> W64.zero 
    ].
proof.
proc => /=.
seq 18 : #pre.
  + inline; auto; while (true); auto => />; while (true); auto => />.
seq 1 : (#pre /\ to_list idx_bytes = sub sk 0 3).
  + auto => /> &hr *.
    apply (eq_from_nth witness); first by rewrite size_to_list size_sub.
    rewrite size_to_list => j?.
    by rewrite get_to_list initiE // nth_sub.
seq 1 : (#pre /\ idx = W64ofBytes (sub sk 0 3)); first by ecall (ull_to_bytes_correct_ idx_bytes); auto => /> /#.
conseq (: 2 ^ XMSS_FULL_HEIGHT < to_uint idx /\  to_list idx_bytes = sub sk 0 3 /\ idx = W64ofBytes (sub sk 0 3) ==> _).
  + by auto => /> &hr ? <-.
rcondt 1.
  + auto => /> &hr.
    rewrite /XMSS_FULL_HEIGHT /= => H?. 
    rewrite uleE of_uintK /(`<<`) ifT //= /#.
seq 4 : (2 ^ XMSS_FULL_HEIGHT < to_uint idx).
  + wp. 
    call (: true); first by while (true); auto => />.
    wp.
    call (: true); first by while (true); auto => />.
    by skip.
seq 1 : (#pre /\ #post /\ exit_0 = W8.one); last by rcondf 1; auto.
rcondt 1; auto => /> ?; rewrite /XMSS_FULL_HEIGHT /= => ?; last by smt(@W64 pow2_64).
by rewrite /(`<<`) ifT // ultE /= /#.
qed.


op load_message (mem : global_mem_t) (ptr : W64.t) (len : W64.t) =
  mkseq (fun (i : int) => mem.[to_uint ptr + i]) (to_uint len).


(*
proc __xmssmt_core_sign (sk:W8.t Array131.t, sm_ptr:W64.t, smlen_ptr:W64.t,
                           m_ptr:W64.t, mlen:W64.t) : W8.t Array131.t * W64.t 

proc sign(sk : xmss_sk, m : msg_t) : sig_t * xmss_sk
*)

lemma sign_correct mem (_sk : xmss_sk, _sm_ptr _smlen_ptr _m_ptr _mlen : W64.t) :
    n = XMSS_N /\ 
    d = XMSS_D /\
    h = XMSS_FULL_HEIGHT /\
    prf_padding_val = XMSS_HASH_PADDING_PRF /\ 
    padding_len = XMSS_PADDING_LEN =>
    equiv [
      M(Syscall).__xmssmt_core_sign ~ XMSS_MT_PRF.sign :

      Glob.mem{1} = mem /\

      arg{1}.`1 = DecodeSkNoOID _sk /\
      arg{1}.`2 = _sm_ptr /\
      arg{1}.`3 = _smlen_ptr /\
      arg{1}.`4 = _m_ptr /\
      arg{1}.`5 = _mlen  /\

      arg{2}.`1 =_sk /\
      arg{2}.`2 = load_message Glob.mem{1} _m_ptr _mlen /\

      valid_ptr_i arg{1}.`5 2500 /\
      to_uint _sm_ptr + XMSS_SIG_BYTES <= W64.max_uint /\
      0 <= to_uint _mlen <= W64.max_uint - XMSS_SIG_BYTES /\
      0 <= to_uint sk{2}.`idx < 2^XMSS_FULL_HEIGHT - 1 (* ensures that the maximum number of signatures was not yet reached *)
      ==>
      res{1}.`1 = DecodeSkNoOID res{2}.`2 /\
      res{1}.`2 = W64.zero /\
      res{2}.`1 = EncodeSignature  (load_message Glob.mem{1} _sm_ptr (W64.of_int XMSS_SIG_BYTES))
    ].
proof.
rewrite /XMSS_N /XMSS_D /XMSS_TREE_HEIGHT /XMSS_FULL_HEIGHT => [#] n_val d_val h_val ??.
proc => /=.
seq 11 0 : #pre; first by auto.

seq 2 0 : (
  #pre /\ 
  exit_0{1} = W8.zero /\
  ots_addr{1} = zero_addr
); first by inline {1} M(Syscall).__zero_address_; wp; ecall {1} (zero_addr_res addr{1}); auto.

seq 1 0 : #pre.
    + inline {1}; auto => /> *.
      smt(zero_addr_setZero).

swap {2} 1 3.

seq 0 1 : (#pre /\ ots_addr{1} = address{2}); first by auto.

seq 0 2 : (
  #pre /\
  val root{2} = sub sk{1} (XMSS_INDEX_BYTES + 2 * n) n /\
  val sk_prf{2} = sub sk{1} (XMSS_INDEX_BYTES +  n) n
).
    + auto => /> &1 &2 *.
      rewrite /DecodeSkNoOID.
      split; (
           apply (eq_from_nth witness); [by rewrite valP size_sub /# | rewrite valP n_val => i?];
           rewrite nth_sub // get_of_list 1:/# /= /XMSS_INDEX_BYTES;
           rewrite nth_cat ifT /=; [by rewrite !size_cat !valP size_take //= size_W32toBytes /# |];
           rewrite nth_cat !size_cat size_EncodeIdx !valP
      ).
         - rewrite ifF /#.
         - rewrite nth_cat !size_cat size_EncodeIdx !valP ifT 1:/# ifF 1:/# /#.
 
seq 0 1 : (
    #pre /\ 
    idx{2} = sk{2}.`idx /\                    
    EncodeIdx idx{2} = (sub sk{1} 0 XMSS_INDEX_BYTES) /\
    0 <= to_uint idx{2} <= 1048575
). 
    + auto => /> &1 *; split => [| /#].
      apply (eq_from_nth witness); first by rewrite size_sub 1:/# size_EncodeIdx.
      rewrite size_EncodeIdx /XMSS_INDEX_BYTES => j?.
      rewrite nth_sub // /DecodeSkNoOID => />.
      rewrite get_of_list 1:/#.
      do (rewrite nth_cat ifT; [by rewrite !size_cat !valP size_EncodeIdx /# |]).
      by rewrite nth_cat ifT; first by rewrite size_EncodeIdx /#.
       
seq 1 0 : (
    #{/~Glob.mem{1} = mem}pre /\
    touches mem Glob.mem{1} (to_uint sm_ptr{1}) (to_uint mlen{1})
); first by admit.

seq 3 0 : (
  #pre /\
  touches mem Glob.mem{1} (to_uint smlen_ptr{1}) 0 
).
    + auto => /> &1 &2 *.
      do split; admit.

seq 1 0 : (#pre /\ to_list idx_bytes{1} = EncodeIdx sk{2}.`idx).
    + auto => /> &1 &2 *.
      apply (eq_from_nth witness); first by rewrite size_to_list size_EncodeIdx.
      rewrite size_to_list => j?.
      rewrite get_to_list initiE // /DecodeSkNoOID get_of_list 1:/#.
      do 3! (rewrite nth_cat ifT; first by rewrite !size_cat !valP /= size_EncodeIdx /#).
      by rewrite nth_cat ifT; [by rewrite size_EncodeIdx /# |].

seq 1 0 : (#pre /\ to_uint idx{1} = to_uint idx{2}).
    + ecall {1} (ull_to_bytes_correct idx_bytes{1}).
      auto => /> &1 &2 *.
      admit.

rcondf {1} 1.
    + auto => /> &hr ??????????????H.
      rewrite uleE /(`<<`) /= -ltzNge H /#.

rcondt {1} 1.
    + auto => /> &hr *.
      smt(@W8).

seq 28 14 : (#{/~r{1} = W64.zero}post); last by auto.
 
seq 26 14 : (sk{1} = DecodeSkNoOID sk{2} /\ sig{2} = EncodeSignature (to_list signature{1})); last first.
    + conseq (: _ ==> to_list signature {1} = load_message Glob.mem{1} _sm_ptr ((of_int XMSS_SIG_BYTES))%W64).
         * by auto => /> *; congr.
      while {1} (
          #pre /\
          0 <= i{1} <= 4963 /\
          sub signature{1} 0 i{1} = sub_list (load_message Glob.mem{1} _sm_ptr ((of_int XMSS_SIG_BYTES))%W64) 0 i{1}
      )
      (4963 - i{1}); last first.
         * auto => /> &1 *.
           split.
               - apply (eq_from_nth witness); first by rewrite size_sub // size_sub_list.
                 rewrite size_sub // /#. 
               - move => memL iL *. 
                 split => [/# | ???].
                 have ->: iL = 4963 by smt().
                 have ->: sub signature{1} 0 4963 = to_list signature{1}.
                    + apply (eq_from_nth witness); first by rewrite size_to_list size_sub.
                      rewrite size_sub // => j?.
                      by rewrite get_to_list nth_sub.
                 move => ->.
                 apply (eq_from_nth witness); first by rewrite size_sub_list // /load_message size_mkseq /XMSS_SIG_BYTES /#.
                 rewrite size_sub_list // => j?.
                 by rewrite /sub_list nth_mkseq.
         * auto => /> &hr *. 
           do split; 1,2,4: by smt().
           apply (eq_from_nth witness); first by rewrite size_sub 1:/# size_sub_list /#.
           rewrite size_sub 1:/# => j?.
           rewrite nth_sub 1:/# /sub_list nth_mkseq 1:/# /= /load_message nth_mkseq /=.
               - rewrite of_uintK /#.
           rewrite /storeW8 get_setE //.
           case (i{hr} = j) => [-> | ?]; admit. (* tenho smptr e smptr{1}, quando nao tenho garantias que sejam iguais *)
seq 1 0 : (#pre /\ sub signature{1} 0 XMSS_INDEX_BYTES = EncodeIdx sk{2}.`idx).
    + auto => /> &1 &2 ?????????????H?.
      apply (eq_from_nth witness); first by rewrite size_sub // size_EncodeIdx /#.
      rewrite size_sub // => j?.
      by rewrite nth_sub // initiE 1:/# /= ifT 1:/# /copy_8 -get_to_list H.

seq 2 1 : (#pre /\ to_uint t64{1} = to_uint idx_new{2}); first by auto => /> *; rewrite !to_uintD_small /#.

seq 2 1 : (
    #{/~to_list idx_bytes{1} = EncodeIdx sk{2}.`Types.idx}
     {/~to_uint sk{2}.`Types.idx < 1048575}pre /\
     to_uint sk{2}.`Types.idx <= 1048575
).
    + auto => />.
      admit.

seq 1 1 : (#pre /\ to_list index_bytes{1} = val idx_bytes{2}).
    + admit.

seq 2 1 : (#pre /\ to_list buf{1} = val _R{2}).

    + inline {1} M(Syscall).__prf_ M(Syscall)._prf; wp; sp.
      exists * in_00{1}, key0{1}; elim * => _P1 _P2.
      call {1} (prf_correctness _P1 _P2) => [/# |].  
      skip => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 ->.
      do split; first by smt(@NBytes).
          - 







search (<) [!].




















    + exists * sm_ptr{1}, m_ptr{1}, mlen{1}.
      elim * => P0 P1 P2.
      call {1} (memcpy_u8pu8p_touches mem P0 P1 P2).
      skip => /> *.
      do split.
          * smt(@W64 pow2_64).
          * admit. (* 0 <= to_uint _sm_ptr + to_uint _mlen => to_uint _sm_ptr + to_uint _mlen < 18446744073709551615  ==> Add to precondition *)
          * admit. (* to_uint _sm_ptr + 4963 + to_uint _mlen < 18446744073709551615 ==> Add to precondition *)
          * move => ????.
            rewrite /touches /load_message => H.
            apply (eq_from_nth witness); first by rewrite !size_mkseq.
            rewrite size_mkseq (: max 0 (to_uint _mlen) = to_uint _mlen) 1:/# => i?.
            rewrite !nth_mkseq // /=.
            admit.


seq 2 0 : (#pre /\ to_uint t64{1} = to_uint mlen{1} + XMSS_SIG_BYTES).
    + auto => /> *.
      rewrite /XMSS_SIG_BYTES to_uintD_small of_uintK // /#.

seq 1 0 : (#pre /\ to_uint (loadW64 Glob.mem{1} (to_uint smlen_ptr{1})) = to_uint mlen{1} + XMSS_SIG_BYTES).
  + auto => /> &1 *.
    split.


swap {2} 2 -1.

seq 0 1 : (#pre /\ ots_addr{1} = address{2}); first by auto.

seq 0 1 : (
    #pre /\ 
    EncodeIdx idx{2} = (sub sk{1} 0 XMSS_INDEX_BYTES) /\
    0 <= to_uint idx{2} <= 1048575
).
    + auto => /> &1 *.
      rewrite /DecodeSkNoOID. admit.
(*
      apply (eq_from_nth witness); first by rewrite size_EncodeIdx size_sub // /#.
      rewrite size_EncodeIdx /XMSS_INDEX_BYTES => i?.
      rewrite nth_sub //= get_of_list 1:/# nth_cat ifT.
         * rewrite !size_cat size_take // !valP sizeW32toBytes /#.
      rewrite nth_cat ifT.
         * rewrite !size_cat size_take // !valP sizeW32toBytes /#.
      rewrite nth_cat ifT.
         * rewrite !size_cat size_take // !valP sizeW32toBytes /#.
      rewrite nth_cat ifT.
         * rewrite size_take // sizeW32toBytes /#.
      by rewrite /EncodeIdx /XMSS_INDEX_BYTES.
*)

seq 0 1 : (
  #pre /\
  val root{2} = sub sk{1} (XMSS_INDEX_BYTES + 2 * n) n
).
    + auto => /> &1 &2 *.
      rewrite /DecodeSkNoOID.
      apply (eq_from_nth witness); first by rewrite valP size_sub /#.
      rewrite valP n_val => i?.
      rewrite nth_sub // get_of_list /= 1:/# nth_cat.
      rewrite ifT.
         * rewrite /XMSS_INDEX_BYTES !size_cat size_take // size_W32toBytes !valP /#.
      rewrite nth_cat ifF.
         * rewrite /XMSS_INDEX_BYTES !size_cat size_take // size_W32toBytes !valP /#.
      congr.
      rewrite !size_cat valP size_take 1:/# size_W32toBytes /XMSS_INDEX_BYTES /= valP /#.

seq 0 1 : (
    #pre /\ 
    val sk_prf{2} = sub sk{1} (XMSS_INDEX_BYTES +  n) n
).
    + auto => /> &1 &2 *.
      rewrite /DecodeSkNoOID.
      apply (eq_from_nth witness); first by rewrite valP size_sub /#.
      rewrite valP n_val => i?.
      rewrite nth_sub // get_of_list 1:/# /= /XMSS_INDEX_BYTES.
      rewrite nth_cat ifT.
         * rewrite !size_cat !valP size_take //= size_W32toBytes /#.
      rewrite nth_cat ifT.
         * rewrite !size_cat !valP size_take //= size_W32toBytes /#.
      rewrite nth_cat ifF.
         * rewrite !size_cat !valP size_take //= size_W32toBytes /#.
      congr.
      rewrite !size_cat valP size_take // size_W32toBytes /=/#.

seq 2 0 : (#pre /\ to_uint idx{1} = to_uint idx{2}).
    + admit.

seq 0 1 : (#pre /\ to_uint idx_new{2} = to_uint idx{2} + 1).
    + auto => /> &1 &2 *.
      rewrite to_uintD_small //=/#.
 
rcondt {1} 1.
    + auto => /> &1 ?????????????H?*.
      rewrite /(`<<`) /= uleE of_uintK H (: 1048575 %% W64.modulus = 1048575) 1:/#. 
      admit.

      

seq 1 0 : (#pre /\ idx_bytes{1} = W32toBytes sk{2}.`Types.idx).
 
seq 2 1 : (#pre /\ to_uint idx{1} = sK.`ty{2}).
  + ecall {1} (ull_to_bytes_correct idx_bytes{1}).
    auto => /> &1 *. 
    rewrite /DecodeSkNoOID.
    admit.
 
rcondt {1} 1.
  + auto => /> &hr *.
    rewrite uleE of_uintK /(`<<`) //=. (* 1048575 <= to_uint idx{hr} *) 
    admit.









 





seq 13 5 : (
  #pre /\
  exit_0{1} = W8.zero /\
  ots_addr{1} = zero_addr /\
  
  idx{2} = sk{2}.`Types.idx /\
  idx{2} = W32ofBytes (sub sk{1} 0 4) /\

  address{2} = zero_addr /\
  root{2} = sk{2}.`sk_root /\
  sk_prf{2} = sk{2}.`Types.sk_prf /\

  idx_new{2} = idx{2} + W32.one
). 
    + inline {1} 13.
      wp.
      ecall {1} (zero_addr_res addr{1}).
      auto => /> *.
      rewrite /DecodeSkNoOID.


   
      admit.

seq 1 0 : #pre.
    + inline {1}; auto => /> *; by apply zero_addr_setZero.

seq 0 1 : (
  #{/~idx{2} = sk{2}.`Types.idx}
   {/~sk{2} = _sk}
   {/~0 <= to_uint sk{2}.`Types.idx < 2 ^ XMSS_FULL_HEIGHT - 1}pre /\ 
  sk{2} = {| _sk with idx=idx_new{2} |} /\
  0 < to_uint sk{2}.`Types.idx <= 2 ^ XMSS_FULL_HEIGHT 
).
    + auto => /> ?????H?. 
      rewrite /XMSS_FULL_HEIGHT //= in H.
      rewrite /XMSS_FULL_HEIGHT to_uintD.
      do split => *; 1,3,4: by smt(@W32 pow2_32). 
      simplify.
      admit. (* Rever: Isto e falso *)



seq 1 0 : (#pre).
    + inline; wp; sp. 
      while {1} (true) (to_uint bytes1{1} - to_uint i0{1}); auto => /> *; first by smt(@W64 pow2_64).
      split; first by rewrite ultE /#.
      rewrite ultE => ?. 
      congr.
      admit. (* This is false *)

seq 2 0 : (#pre /\ to_uint t64{1} = to_uint mlen{1} + XMSS_SIG_BYTES).
  + auto => /> *.
    rewrite /XMSS_SIG_BYTES to_uintD_small of_uintK /#.

seq 1 0 : (#pre).
    + auto => /> &1 *.
         admit.



seq 1 1 : (#pre /\ to_list idx_bytes{1} = sub sk{1} 0 XMSS_INDEX_BYTES).
    + auto => /> &1 &2 *.
      apply (eq_from_nth witness); first by rewrite size_to_list size_sub /#.
      rewrite size_to_list => i?.
      rewrite get_to_list initiE // /DecodeSkNoOID get_of_list 1:/# nth_sub 1:/# get_of_list // /#.

seq 1 0 : (#pre /\ to_uint idx{1} = to_uint sk{2}.`Types.idx /\ to_uint idx{1} < 2 ^ XMSS_FULL_HEIGHT - 1).

    + admit.



(* We dont enter this if statement because we assumed that the index is valid *)
rcondf {1} 1.
    + auto => /> &hr ???????????H.
      rewrite /XMSS_FULL_HEIGHT /= in H.
      rewrite uleE of_uintK /(`<<`) ifT // /#.

(* We enter this if statement because we assumed that the index is valid *)
rcondt {1} 1; first by auto => /> ; smt(@W8).

seq 2 0 : (#pre /\ sub signature{1} 0 XMSS_INDEX_BYTES = to_list idx_bytes{1}).
    + wp.
      inline {1} 1.
      inline {1} 5.
      wp.
      exists * idx_bytes{1}; elim * => P0.
      ecall {1} (_memcpy_u8u8_3_3_post_p P0).
      auto => /> &1 ????????? H *. 
      rewrite H.
      apply (eq_from_nth witness); first by rewrite /XMSS_INDEX_BYTES !size_sub.
      rewrite size_sub // /XMSS_INDEX_BYTES => i?.
      rewrite !nth_sub // /DecodeSkNoOID initiE 1:/# get_of_list 1:/# /= ifT //.
      rewrite nth_cat ifT.
           * rewrite !size_cat !valP n_val size_take // sizeW32toBytes ifT /#.
      rewrite nth_cat ifT.
           * rewrite !size_cat !valP n_val size_take // sizeW32toBytes ifT /#.
      rewrite nth_cat ifT.
           * rewrite !size_cat !valP n_val size_take // sizeW32toBytes ifT /#.
      rewrite nth_cat ifT.
           * rewrite size_take // sizeW32toBytes ifT /#.
      rewrite nth_take // 1:/#.
      rewrite -get_to_list H.
      rewrite !nth_sub // /DecodeSkNoOID initiE 1:/# /=.
      rewrite nth_cat ifT.
           * rewrite !size_cat !valP n_val size_take // sizeW32toBytes ifT /#.
      rewrite nth_cat ifT.
           * rewrite !size_cat !valP n_val size_take // sizeW32toBytes ifT /#.
      rewrite nth_cat ifT.
           * rewrite !size_cat !valP n_val size_take // sizeW32toBytes ifT /#.
      rewrite nth_cat ifT.
           * rewrite size_take // sizeW32toBytes ifT /#.
      rewrite nth_take // /#.

seq 27 11 : (#{/~r{1} = W64.zero}post); last by auto => />.

seq 2 0 : (#{/~to_uint t64{1} = to_uint mlen{1} + XMSS_SIG_BYTES}pre /\ 
           t64{1} = idx{1} + W64.one); first by auto.

seq 5 1 : (#pre /\ to_list buf{1} = val _R{2}).
    + admit.

seq 2 0 : (#pre /\ sub signature{1} XMSS_INDEX_BYTES n = val _R{2}).
    + wp.
      exists * buf{1}; elim * => P1.
      call {1} (_x_memcpy_u8u8_post P1).
      auto => /> &1 &2 ???????????H0 H1 ; split.
           * apply (eq_from_nth witness); first by rewrite size_to_list size_sub.
             rewrite size_sub // /XMSS_INDEX_BYTES => i?.             
             rewrite nth_sub // initiE 1:/# /= ifF 1:/#.
             rewrite (: idx_bytes{1}.[i] = nth witness (to_list idx_bytes{1}) i) 1:/# -H0 nth_sub //.
           * apply (eq_from_nth witness); first by rewrite size_sub 1:/# valP.
             rewrite size_sub 1:/# n_val => i?.
             by rewrite nth_sub // initiE 1:/# /= ifT 1:/# -H1 /XMSS_INDEX_BYTES get_to_list.

seq 1 0 : (#{/~t64{1} = idx{1} + W64.one}pre /\ to_list pub_root{1} = val root{2}).
    + auto => /> &1 &2 *.
      apply (eq_from_nth witness); first by rewrite size_to_list valP n_val.
      rewrite size_to_list => i?.
      rewrite get_to_list initiE //= /DecodeSkNoOID get_of_list 1:/# nth_cat ifT.
          * rewrite !size_cat !valP n_val size_take //= sizeW32toBytes ifT /#.
      rewrite nth_cat ifF.
          * rewrite !size_cat !valP n_val size_take //= sizeW32toBytes ifT /#.
      rewrite !size_cat !valP n_val size_take // sizeW32toBytes ifT /#.

seq 3 2 : (#pre /\ val _M'{2} = to_list mhash{1}).
    + wp.
      admit.

seq 2 0 : #pre; first by inline {1}; auto => /> &1 &2 *;rewrite !zero_addr_setZero //.

seq 2 1 : (#pre /\ to_uint idx_tree{1} = to_uint idx_tree{2}).
    + auto => /> &1 &2 *. 
      rewrite  shr_div of_uintK //= h_val d_val /= /W32.
      admit.

seq 2 1 : (#pre /\ to_uint idx_leaf{1} = to_uint idx_leaf{2}).
    + auto => /> &1 &2 *.
      admit.

seq 1 2 : (#{/~ots_addr{1} = zero_addr}
            {/~address{2} = zero_addr}pre /\  
           address{2} = ots_addr{1}).
    + inline {1}; auto => /> &1 &2 *.
      rewrite /set_tree_addr /set_layer_addr.
      rewrite tP => i?.
      rewrite get_setE //.
      case (i = 2) => *.
         * rewrite get_setE // ifT // #smt:(@W32 pow2_32).
      rewrite get_setE //.
      case (i = 1) => *.
         * rewrite get_setE // ifF 1:/# get_setE // ifT //. 
           rewrite (: 63 = 2^6 - 1) 1:/# and_mod // of_uintK.
           rewrite /truncateu8 of_uintK //=.
           rewrite /truncateu32 shr_div of_uintK /= /#. 
      rewrite get_setE //.
      case (i = 0) => *.
         * by rewrite get_setE // ifF 1:/# get_setE // ifF 1:/# zero_addr_i.
      by rewrite get_setE // ifF 1:/# get_setE // ifF 1:/#.

seq 5 4 : (
            to_uint _sm_ptr + XMSS_SIG_BYTES <= W64.max_uint /\
            sm_ptr{1} = _sm_ptr /\ 
            sk{1} = DecodeSkNoOID sk{2} /\ 
            sig{2} = EncodeSignature (to_list signature{1})
); last first.

while {1}
(#pre /\
 0 <= i{1} <= XMSS_SIG_BYTES /\
 forall (k : int), 0 <= k < i{1} => loadW8 Glob.mem{1} (to_uint sm_ptr{1} + k) = signature{1}.[k])
(XMSS_SIG_BYTES - i{1}); last first.
  + auto => /> &1 *.
    split => [/# | mem i].
    split => [/# | ???].
    have ->: i = XMSS_SIG_BYTES by smt().
    rewrite /XMSS_SIG_BYTES => H.
    congr.
    apply (eq_from_nth witness); first by rewrite size_to_list /load_message size_mkseq of_uintK /=.
    rewrite size_to_list => j?.
    by rewrite /load_message get_to_list nth_mkseq //= -H.
  + auto => /> &hr H?H0 H1?. 
    rewrite /XMSS_SIG_BYTES in H0.
    rewrite /XMSS_SIG_BYTES in H.
    do split; 1,2,4: by smt().
    move => k??.
    rewrite /loadW8 /storeW8 get_setE. 
    
    case (k = i{hr}) => [-> | ?].
      * rewrite ifT // to_uintD of_uintK #smt:(@W64 pow2_64).
      * rewrite ifF; [by rewrite to_uintD of_uintK #smt:(@W64 pow2_64) |].
        rewrite -H1 // /#.
    

admit.
qed.



(* ========================================================================================================================================= *)


swap {2} 2 - 1.
seq 1 1 : (
    #pre /\
    to_list idx_bytes{1} = val idx_bytes{2}
); first by admit. (* este idx e o original ou o que foi incrementado? ++> O original *)

seq 0 1 : (#pre /\ sk{1} = DecodeSkNoOID sk{2}). (* Isto nao e #pre *)
    + auto => /> &1 *; do split => />. 
        * admit.
        * rewrite to_uintD /#.
        * move => ?. rewrite /XMSS_FULL_HEIGHT /= to_uintD. admit.
        * admit.
        * admit.
        * admit.

seq 1 0 : (#pre /\ to_list sk_prf{1} = val sk_prf{2}).
    + auto => /> &1 &2 *.
      apply (eq_from_nth witness); first by rewrite valP n_val _to_list.
      rewrite size_to_list => j?. 
      rewrite get_to_list initiE // => />.
      rewrite /DecodeSkNoOID get_of_list 1:/#.
      rewrite nth_cat !size_cat !valP n_val sizeW32toBytes /= ifT 1:/#.
      rewrite nth_cat !size_cat !valP n_val sizeW32toBytes /= ifT 1:/#.
      by rewrite nth_cat !size_cat !valP n_val sizeW32toBytes /= ifF 1:/#.

seq 1 1 : (#pre /\ to_list buf{1} = val _R{2}).
    + inline {1} M(Syscall).__prf_ M(Syscall)._prf; wp; sp.
      exists * in_00{1}, key0{1}; elim * => _P1 _P2; call {1} (prf_correctness _P1 _P2) => [/# |]. 
      skip => /> &1 &2  ???? H0 H1 H2 H3 H4 H5 H6; do split. 
        * rewrite H5 #smt:(@NBytes).
        * rewrite H6 #smt:(@NBytes).
        * by move => ???? ->.
admit.
qed.
