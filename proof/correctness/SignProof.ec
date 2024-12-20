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

(*
proc __xmssmt_core_sign (sk:W8.t Array131.t, sm_ptr:W64.t, smlen_ptr:W64.t,
                           m_ptr:W64.t, mlen:W64.t) : W8.t Array131.t * W64.t 

proc sign(sk : xmss_sk, m : msg_t) : sig_t * xmss_sk
*)

lemma sign_correct (_sk : xmss_sk, _sm_ptr _smlen_ptr _m_ptr _mlen : W64.t) :
    n = XMSS_N /\ 
    d = XMSS_D /\
    h = XMSS_FULL_HEIGHT /\
    prf_padding_val = XMSS_HASH_PADDING_PRF /\ 
    padding_len = XMSS_PADDING_LEN =>
    equiv [
      M(Syscall).__xmssmt_core_sign ~ XMSS_MT_PRF.sign :

      arg{1}.`1 = DecodeSkNoOID _sk /\
      arg{1}.`2 = _sm_ptr /\
      arg{1}.`3 = _smlen_ptr /\
      arg{1}.`4 = _m_ptr /\
      arg{1}.`5 = _mlen  /\

      arg{2}.`1 =_sk /\
      arg{2}.`2 = load_buf Glob.mem{1} _m_ptr (to_uint _mlen) /\

      valid_ptr_i arg{1}.`5 2500 /\
      to_uint _sm_ptr + XMSS_SIG_BYTES <= W64.max_uint /\
      0 <= to_uint _mlen <= W64.max_uint - XMSS_SIG_BYTES /\
      0 <= to_uint sk{2}.`idx < 2^XMSS_FULL_HEIGHT - 1 (* ensures that the maximum number of signatures was not yet reached *)
      ==>
      res{1}.`1 = DecodeSkNoOID res{2}.`2 /\
      res{1}.`2 = W64.zero /\
      res{2}.`1 = EncodeSignature  (load_buf Glob.mem{1} _sm_ptr XMSS_SIG_BYTES)
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
  #pre /\
  load_buf Glob.mem{1} sm_ptr{1} (to_uint mlen{1}) = m{2}
).
    + inline M(Syscall)._x__memcpy_u8pu8p.
      inline M(Syscall)._memcpy_u8pu8p.
      wp; sp.
      exists * Glob.mem{1}, out_ptr0{1}, out_offset0{1}, in_ptr0{1}, in_offset0{1}, bytes0{1}.
      elim * => P0 P2 P3 P4 P5 P6.
      call {1} (p_memcpy_mem_mem P0 P2 P3 P4 P5 P6). 
      skip => /> &2 *.
      do split.
        + admit.
        + admit.
        + admit.
        + admit.
        + admit.
        + admit.
        + admit.
        + admit.
        + move => *; split; (
            apply (eq_from_nth witness); 
            [by rewrite !size_load_buf | rewrite size_load_buf // => ? /#]
          ).


        


seq 3 0 : #pre. (* o valor escrito p memoria aqui nao me interessa *)
    + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 *.
      split; (
         apply (eq_from_nth witness); [by rewrite !size_load_buf // | rewrite size_load_buf // => j?];
         rewrite nth_load_buf //
      ); last by admit.
         * rewrite /load_buf /storeW64 nth_mkseq //= /loadW8. 
           rewrite get_storesE.
           rewrite ifF //=. admit.


seq 1 0 : (#pre /\ to_list idx_bytes{1} = EncodeIdx sk{2}.`idx).
    + auto => /> &1 &2 *.
      apply (eq_from_nth witness); first by rewrite size_to_list size_EncodeIdx.
      rewrite size_to_list => j?.
      rewrite get_to_list initiE // /DecodeSkNoOID get_of_list 1:/#.
      do 3! (rewrite nth_cat ifT; first by rewrite !size_cat !valP /= size_EncodeIdx /#).
      by rewrite nth_cat ifT; [by rewrite size_EncodeIdx /# |].

seq 1 0 : (#pre /\ to_uint idx{1} = to_uint idx{2}).
    + ecall {1} (ull_to_bytes_correct idx_bytes{1}).
      auto => /> &1 &2 ???????????? H. 
      pose x := (W64ofBytes (to_list idx_bytes{1})).
      pose y :=  _sk.`Types.idx.
      rewrite (to_uint_W64_W32 x y). admit. (* FIXME: *)
      rewrite to_uint_zeroextu64.        
      reflexivity.

rcondf {1} 1.
    + auto => /> &hr ?????????????H.
      rewrite uleE /(`<<`) /= -ltzNge H /#.

rcondt {1} 1.
    + auto => /> &hr *.
      smt(@W8).

seq 27 14 : (#{/~r{1} = W64.zero}post); last by auto.
 
seq 25 14 : (sk{1} = DecodeSkNoOID sk{2} /\ sig{2} = EncodeSignature (to_list signature{1})); last first.
    + conseq (: _ ==> to_list signature {1} = load_buf Glob.mem{1} _sm_ptr XMSS_SIG_BYTES).
         * by auto => /> *; congr.
      while {1} (
          #pre /\
          0 <= i{1} <= 4963 /\
          sub signature{1} 0 i{1} = sub_list (load_buf Glob.mem{1} _sm_ptr (XMSS_SIG_BYTES)) 0 i{1}
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
           rewrite nth_sub 1:/# /sub_list nth_mkseq 1:/# /= /load_message nth_mkseq /= 1:/#.
           rewrite /storeW8 /loadW8 get_setE //.
           case (i{hr} = j) => [-> | ?]; admit. (* tenho smptr e smptr{1}, quando nao tenho garantias que sejam iguais *)

seq 1 0 : (#pre /\ sub signature{1} 0 XMSS_INDEX_BYTES = EncodeIdx sk{2}.`idx).
    + auto => /> &1 &2 ????????????H?.
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
      ecall {1} (ull_to_bytes_3_correct t64{1}).
      skip => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 result H16.
      do split.
         - rewrite tP => j?. admit.
         - admit.
         - smt(@W32 pow2_32).
         - apply (eq_from_nth witness); first by rewrite valP n_val size_sub.
           rewrite valP n_val => j?.
           rewrite !nth_sub //.
           rewrite initiE 1:/# /= => />.
           rewrite initiE 1:/# /= => />.
           rewrite ifF 1:/#.
           rewrite nth_cat !size_cat !valP n_val /XMSS_INDEX_BYTES size_EncodeIdx ifT 1:/#.
           rewrite nth_cat !size_cat !valP n_val /XMSS_INDEX_BYTES size_EncodeIdx ifF 1:/#.
           rewrite H6 /DecodeSkNoOID.
           rewrite !nth_sub // 1:/#.
           rewrite initiE 1:/# /= => />.
           rewrite nth_cat !size_cat !valP n_val /XMSS_INDEX_BYTES size_EncodeIdx ifT 1:/#.
           rewrite nth_cat !size_cat !valP n_val /XMSS_INDEX_BYTES size_EncodeIdx ifF 1:/#.
           congr => /#.
         - apply (eq_from_nth witness); first by rewrite valP n_val size_sub.
           rewrite valP n_val => j?.
           rewrite !nth_sub //.
           rewrite initiE 1:/# /= => />.
           rewrite initiE 1:/# /= => />.
           rewrite ifF 1:/#.
           rewrite nth_cat !size_cat !valP n_val /XMSS_INDEX_BYTES size_EncodeIdx ifT 1:/#.
           rewrite nth_cat !size_cat !valP n_val /XMSS_INDEX_BYTES size_EncodeIdx ifT 1:/#.
           rewrite H7 /DecodeSkNoOID.
           rewrite !nth_sub // 1:/#.
           rewrite initiE 1:/# /= => />.
           rewrite nth_cat !size_cat !valP n_val /XMSS_INDEX_BYTES size_EncodeIdx ifT 1:/#.
           rewrite nth_cat !size_cat !valP n_val /XMSS_INDEX_BYTES size_EncodeIdx ifT 1:/#.
           congr => /#.
         - admit.
         - rewrite -H14.
           apply (eq_from_nth witness); first by rewrite !size_sub /#.
           rewrite size_sub 1:/# /XMSS_INDEX_BYTES => j?.
           rewrite !nth_sub // initiE 1:/# /= ifT //.
           have ->: result.[j] = nth witness (to_list result) j by rewrite get_to_list.
           have ->: signature{1}.[j] = nth witness (sub signature{1} 0 XMSS_INDEX_BYTES) j by rewrite nth_sub.
           rewrite H16 H14.
           admit.
           (* TODO: Escrever este lemma no ficheiro repr2.ec *)
         - admit.
         - admit.

      

seq 1 1 : (#pre /\ to_list index_bytes{1} = val idx_bytes{2}).
    + admit.

seq 2 1 : (#pre /\ to_list buf{1} = val _R{2}).
    + inline {1} M(Syscall).__prf_ M(Syscall)._prf; wp; sp.
      exists * in_00{1}, key0{1}; elim * => _P1 _P2.
      call {1} (prf_correctness _P1 _P2) => [/# |].  
      skip => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13  ->.
      do split; first by smt(@NBytes).
          - apply nbytes_eq.
            rewrite insubdK; first by rewrite /P size_to_list /#.
            apply (eq_from_nth witness); first by rewrite valP n_val size_to_list.
            rewrite valP n_val => j?.
            rewrite get_to_list initiE //= H6.
            by rewrite nth_sub 1:/# /XMSS_INDEX_BYTES n_val /=.
          - by move => ????->.

seq 1 0 : (#pre /\ sub signature{1} XMSS_INDEX_BYTES n = val _R{2}).
    + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14  <-.
      split.
         * rewrite /XMSS_INDEX_BYTES.
           apply (eq_from_nth witness); first by rewrite size_sub // size_EncodeIdx. 
           rewrite size_sub // => i?. 
           rewrite -H12.
           by rewrite !nth_sub //= initiE 1:/# /= ifF 1:/#.
         * apply (eq_from_nth witness); first by rewrite size_to_list size_sub n_val.
           rewrite size_sub n_val // => j?.
           by rewrite nth_sub // initiE 1:/# /= ifT 1:/# /copy_8 /XMSS_INDEX_BYTES.

seq 1 1 : (
    #pre /\ 
    to_list pub_root{1} = val root{2} /\
    val t{2} = val _R{2} ++ val root{2} ++ val idx_bytes{2}
).
    + auto => /> &1 &2 ????? -> *.
      split.
          * apply (eq_from_nth witness); first by rewrite size_to_list size_sub n_val.
            rewrite size_to_list => i?.
            by rewrite get_to_list initiE //= nth_sub 1:/# /XMSS_INDEX_BYTES n_val.
          * rewrite insubdK // /P !size_cat !valP size_sub /#.
    
seq 3 1 : (#pre /\ to_list mhash{1} = val _M'{2}).
    + admit.

seq 2 0 : #pre; first by inline {1}; auto => /> *; smt(zero_addr_setZero).

seq 2 1 : (#pre /\ to_uint idx_tree{1} = to_uint idx_tree{2}).
    + auto => /> &1 &2 ??????????? H *.
      by rewrite h_val d_val /= !to_uint_shr // of_uintK /= H.

seq 2 1 : (#pre /\ to_uint idx_leaf{1} = to_uint idx_leaf{2}).
    + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 *.
      rewrite d_val h_val /= /(`<<`) /= and_comm.
      congr; congr.
      by rewrite /truncateu32 H11 to_uintK.

seq 0 1 : #pre; first by auto => /> *; rewrite /set_layer_addr; smt(zero_addr_setZero).
     
seq 1 1 : (#{/~ots_addr{1} = zero_addr}pre).
    + inline {1}; auto => /> &1 &2 ????????????????????<-?.
      rewrite /set_tree_addr tP => j?.
      rewrite !get_setE //.
      case (j = 1) => [-> | ?].
         * rewrite ifF 1:/# ifF 1:/# /truncateu32.
           congr.
           by rewrite (: 63 = 2^6 -1) 1:/# and_mod //= to_uint_shr /truncateu8 of_uintK of_uintK 1:/#.
      case (j = 2) => [? | //].
      rewrite /truncateu32; smt(@W32 pow2_32).




(* =========================================== fiquei aqui *)

      





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
qed.
