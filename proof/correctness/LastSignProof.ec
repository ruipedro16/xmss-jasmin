pragma Goals : printall.

require import AllCore List RealExp IntDiv Distr DList IntDiv.
from Jasmin require import JModel JArray.

require import Params Types Address Hash LTree XMSS_MT_PRF XMSS_MT_Types XMSS_MT_TreeHash XMSS_MT_Params.
require import XMSS_IMPL Parameters.

require import Repr2. 
require import Utils2.

require import Array3 Array8 Array32 Array64 Array68 Array96 Array131 Array352 Array2144 Array2464 Array4963.
require import WArray32 WArray96 WArray131.

require import Correctness_Address Correctness_Bytes Correctness_Mem Correctness_Hash.
require import DistrUtils.

require import BitEncoding.
(*---*) import BitChunking.

require import TreeSigAuthPathProof. 
require import Bytes.

require import BaseW.

require import FinalTreeHashProof.


pred valid_idx (idx : W32.t) = 0 <= to_uint idx < 2^XMSS_FULL_HEIGHT.

import W8u8.

lemma sign_correct (_sk : xmss_sk, _sm_ptr _smlen_ptr _m_ptr _mlen : W64.t) :
    n = XMSS_N /\ 
    d = XMSS_D /\
    h = XMSS_FULL_HEIGHT /\
    prf_padding_val = XMSS_HASH_PADDING_PRF /\ 
    padding_len = XMSS_PADDING_LEN /\ 
    len = XMSS_WOTS_LEN /\
    w = XMSS_WOTS_W /\
    len1 = XMSS_WOTS_LEN1 /\
    len2 = XMSS_WOTS_LEN2 /\ 
    prf_kg_padding_val = XMSS_HASH_PADDING_PRF_KEYGEN /\
    F_padding_val = XMSS_HASH_PADDING_F /\
    floor (log2 w%r) = XMSS_WOTS_LOG_W /\
    H_msg_padding_val = XMSS_HASH_PADDING_HASH
    =>
    equiv [
      M(Syscall).__xmssmt_core_sign ~ XMSS_MT_PRF.sign :

      arg{1}.`1 = DecodeSkNoOID _sk /\
      arg{1}.`2 = _sm_ptr /\
      arg{1}.`3 = _smlen_ptr /\
      arg{1}.`4 = _m_ptr /\
      arg{1}.`5 = _mlen  /\

      arg{2}.`1 =_sk /\
      arg{2}.`2 = load_buf Glob.mem{1} _m_ptr (to_uint _mlen) /\

      0 < to_uint _mlen < W64.max_uint /\
      0 <= to_uint _sm_ptr + XMSS_SIG_BYTES < W64.max_uint /\
      0 <= to_uint _sm_ptr + XMSS_SIG_BYTES + to_uint _mlen < W64.max_uint /\
      0 <= to_uint _m_ptr + to_uint _mlen < W64.max_uint /\
      0 <= to_uint _m_ptr < W64.max_uint /\
      0 <= to_uint _smlen_ptr < W64.max_uint /\
      0 <= to_uint _smlen_ptr + 8 < W64.max_uint /\

      disjoint_ptr (to_uint _sm_ptr) (XMSS_SIG_BYTES + to_uint _mlen) 
                   (to_uint _m_ptr) (to_uint _mlen) /\

      disjoint_ptr (to_uint _sm_ptr) (XMSS_SIG_BYTES + to_uint _mlen) 
                   (to_uint _smlen_ptr{1}) 8 /\ (* 1 W64 = 8 bytes *)

      disjoint_ptr (to_uint _smlen_ptr) 8
                   (to_uint _m_ptr) (to_uint _mlen) /\

      0 <= to_uint sk{2}.`idx < 2^XMSS_FULL_HEIGHT - 1 
     (* ensures that the maximum number of signatures was not yet reached *)
      ==>
      res{1}.`1 = DecodeSkNoOID res{2}.`2 /\
      res{2}.`1 = EncodeSignature  (load_buf Glob.mem{1} _sm_ptr XMSS_SIG_BYTES)
    ].
proof.
rewrite /XMSS_N /XMSS_D /XMSS_TREE_HEIGHT /XMSS_FULL_HEIGHT /XMSS_WOTS_LEN.
move => [#] n_val d_val h_val ?? len_val *.
proc => /=.  

seq 11 0 : (
  sk{1} = DecodeSkNoOID sk{2} /\
  m{2} = load_buf Glob.mem{1} m_ptr{1} (to_uint mlen{1}) /\

  _sm_ptr = sm_ptr{1} /\ (* need this for #post *)

  (* valid ptr ranges *)
  0 < to_uint mlen{1} < 18446744073709551615 /\
  0 <= to_uint sm_ptr{1} + XMSS_SIG_BYTES < 18446744073709551615 /\
  0 <= to_uint sm_ptr{1} + XMSS_SIG_BYTES + to_uint mlen{1} < 18446744073709551615 /\
  0 <= to_uint m_ptr{1} + to_uint mlen{1} < 18446744073709551615 /\
  0 <= to_uint m_ptr{1} < 18446744073709551615 /\
  0 <= to_uint smlen_ptr{1} < W64.max_uint /\
  0 <= to_uint smlen_ptr{1} + 8 < W64.max_uint /\
 
  (* disjoint pointers *)
  disjoint_ptr (to_uint sm_ptr{1}) (XMSS_SIG_BYTES + to_uint mlen{1})
               (to_uint m_ptr{1}) (to_uint mlen{1}) /\

  disjoint_ptr (to_uint sm_ptr{1}) (XMSS_SIG_BYTES + to_uint mlen{1})
               (to_uint smlen_ptr{1}) 8 /\

  disjoint_ptr (to_uint smlen_ptr{1}) 8 (to_uint m_ptr{1}) (to_uint mlen{1}) /\

  0 <= to_uint sk{2}.`Types.idx  < 1048575   
); first by auto.

seq 2 0 : (
  #pre /\ 
  exit_0{1} = W8.zero /\
  ots_addr{1} = zero_addr
). 
    + inline {1} M(Syscall).__zero_address_; wp.
      ecall {1} (zero_addr_res addr{1}); auto.

seq 1 2 : (
  #pre /\
  address{2} = ots_addr{1} /\
  idx{2} = sk{2}.`Types.idx
).
    + inline {1}; auto => /> &1 &2 *; smt(zero_addr_setZero).

seq 0 3 : (
  #pre /\
  root{2} = sk{2}.`Types.sk_root /\
  sk_prf{2} = sk{2}.`Types.sk_prf /\
  idx_new{2} = idx{2} + W32.one
); first by auto.

(* Aqui copiamos a mensagem para a parte da assinatura *)
seq 1 0 : (
  #pre /\
  load_buf Glob.mem{1} (sm_ptr{1} + (of_int 4963)%W64)  (to_uint mlen{1}) = m{2}
).
    + ecall {1} (memcpy_mem_mem Glob.mem{1} sm_ptr{1} (of_int 4963)%W64 m_ptr{1} W64.zero mlen{1}).
      auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 *.
      do split; 1,2: by smt(). 
      move => H15 H16 H17 H18 memL H19 H20.
      split; (apply (eq_from_nth witness); first by rewrite !size_load_buf; smt(@W64 pow2_64)).
          * rewrite size_load_buf // => j?.
            rewrite !nth_load_buf // H20 // /#.
          * rewrite size_load_buf // => j?.
            rewrite H19 !nth_load_buf // H20 /#. 

seq 3 0 : (
  #pre /\ 
  loadW64 Glob.mem{1} (to_uint smlen_ptr{1}) = mlen{1} + (of_int XMSS_SIG_BYTES)%W64
).
    + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 *.
      do split; last by rewrite load_store_W64.
         - apply (eq_from_nth witness); first by rewrite !size_load_buf // /#.
           rewrite size_load_buf 1:/# => j?.
           rewrite !nth_load_buf //.
           rewrite /storeW64 storesE => />.
           rewrite get_setE ifF 1:/#.
           rewrite get_setE ifF 1:/#.
           rewrite get_setE ifF 1:/#.
           rewrite get_setE ifF 1:/#.
           rewrite get_setE ifF 1:/#.
           rewrite get_setE ifF 1:/#.
           rewrite get_setE ifF 1:/#.
           rewrite get_setE ifF 1:/#.
           reflexivity.

         - apply (eq_from_nth witness); first by rewrite !size_load_buf // /#.
           rewrite size_load_buf 1:/# => j?.
           rewrite !nth_load_buf //.
           rewrite /storeW64 storesE => />. 
           have ->: to_uint (_sm_ptr + (of_int 4963)%W64) + j = 
                    to_uint _sm_ptr + 4963 + j by smt(@W64 pow2_64). 
           rewrite get_setE ifF 1:/#.
           rewrite get_setE ifF 1:/#.
           rewrite get_setE ifF 1:/#.
           rewrite get_setE ifF 1:/#.
           rewrite get_setE ifF 1:/#.
           rewrite get_setE ifF 1:/#.
           rewrite get_setE ifF 1:/#.
           rewrite get_setE ifF 1:/#.
           have ->: Glob.mem{1}.[to_uint _sm_ptr + 4963 + j] = 
                    nth witness 
                    (load_buf Glob.mem{1} (_sm_ptr + (of_int 4963)%W64) (to_uint mlen{1}))
                    j by rewrite nth_load_buf ; smt(@W64 pow2_64).
            by rewrite H19 nth_load_buf.

(* Isto nao e usado *)
seq 0 0 : (
       #{/~loadW64 Glob.mem{1} (to_uint smlen_ptr{1}) = 
           mlen{1} + (of_int XMSS_SIG_BYTES)%W64}pre
); first by auto.


seq 1 0 : (#pre /\ to_list idx_bytes{1} = EncodeIdx sk{2}.`idx).
 + auto => /> &1 &2 *.
   apply (eq_from_nth witness); first by rewrite size_EncodeIdx /XMSS_INDEX_BYTES size_to_list.
   rewrite size_to_list => j?.
   rewrite get_to_list initiE // /DecodeSkNoOID get_of_list 1:/#.
   rewrite nth_cat !size_cat size_EncodeIdx /XMSS_INDEX_BYTES !valP n_val ifT 1:/#.
   rewrite nth_cat !size_cat size_EncodeIdx /XMSS_INDEX_BYTES !valP n_val ifT 1:/#.
   rewrite nth_cat !size_cat size_EncodeIdx /XMSS_INDEX_BYTES !valP n_val ifT 1:/#.
   rewrite nth_cat size_EncodeIdx /XMSS_INDEX_BYTES ifT 1:/#.
   reflexivity.

seq 1 0 : (#pre /\ to_uint idx{1} = to_uint sk{2}.`Types.idx).
  + ecall {1} (bytes_to_ull_correct idx_bytes{1}).
    auto  => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 result ->.
    by rewrite H20 EncodeIdxKancel; first by rewrite /XMSS_FULL_HEIGHT /#.
     

rcondf {1} 1; first by auto => /> *; rewrite uleE of_uintK /(`<<`) /= /#.
rcondt {1} 1; first by auto => /> *; smt(@W8).

seq 25 13 : (
  _sm_ptr = sm_ptr{1} /\
  0 <= to_uint sm_ptr{1} + XMSS_SIG_BYTES < 18446744073709551615 /\ (* valid_ptr *)
  sk{1} = DecodeSkNoOID sk{2} /\
  sig{2} = EncodeSignature (to_list signature{1})
); last first.
  + wp; conseq />.
    while {1} (
      _sm_ptr = sm_ptr{1} /\
      0 <= to_uint sm_ptr{1} + XMSS_SIG_BYTES < 18446744073709551615 /\
      0 <= i{1} <= XMSS_SIG_BYTES /\
      load_buf Glob.mem{1} _sm_ptr i{1} = sub signature{1} 0 i{1}
    ) (XMSS_SIG_BYTES - i{1}); last first.
     - auto => /> &1 *.
       split.
         * apply (eq_from_nth witness); first by rewrite size_load_buf // size_sub.
           rewrite size_load_buf // /#.
         * move => memL iL.
           split => [/# | H0 H1 H2].
           have ->: iL = XMSS_SIG_BYTES by smt().
           move => ->; congr.
           apply (eq_from_nth witness); first by rewrite size_to_list size_sub //.                             rewrite size_to_list => i?.
           by rewrite get_to_list nth_sub 1:/#.
     - auto => /> &hr H0 H1 H2 H3 H4 *.
       do split; 1,2,4: by smt().
       apply (eq_from_nth witness); first by rewrite size_load_buf 1:/# size_sub // /#.
       rewrite size_load_buf 1:/# => j?.
       rewrite nth_sub // nth_load_buf // /storeW8 get_setE.
       have ->: to_uint (_sm_ptr + (of_int i{hr})%W64) = to_uint _sm_ptr + i{hr} by smt(@W64 pow2_64).
       case (j = i{hr}) => [/# |?]; rewrite ifF 1:/# /=.
       have ->: signature{hr}.[j] = nth witness (sub signature{hr} 0 i{hr}) j by rewrite nth_sub // /#.
       rewrite -H4 nth_load_buf // /#.
 
seq 1 0 : (
      #pre /\
      sub signature{1} 0 XMSS_INDEX_BYTES = to_list idx_bytes{1}
).
    + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 *.
      apply (eq_from_nth witness); first by rewrite size_to_list size_sub /#. 
      rewrite size_sub 1:/# /XMSS_INDEX_BYTES => i?.
      by rewrite get_to_list nth_sub // initiE 1:/# /= ifT.
  
seq 2 0 : (
   #pre /\ 
   to_uint t64{1} = to_uint idx_new{2} /\
   truncateu32 t64{1} = idx{2} + W32.one
).
    + auto => /> &1 &2 *; split; first by smt(@W64 pow2_64  @W32 pow2_32). 
      rewrite to_uintW2 //=.
      have ->: truncateu32 W64.one = W32.one by rewrite /truncateu32 of_uintK.
      rewrite /truncateu32.
      have ->: to_uint (idx{1} + W64.one) = to_uint idx{1} + 1 by smt(@W64 pow2_64).
      smt(@W32 pow2_32). 

 
seq 1 0 : (#pre /\ to_list aux_0{1} = EncodeIdx idx_new{2}).
    + ecall {1} (ull_to_bytes_3_correct t64{1}).
      auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 *.
      do split.
        - smt(@W32 pow2_32).
        - rewrite /XMSS_FULL_HEIGHT /=; smt(@W32 pow2_32). (* SMT doesnt work if we dont do this rewrite before *)
        - move => H22 H23 result  Hr. 
          rewrite /XMSS_FULL_HEIGHT /= in H23.
          rewrite /EncodeIdx Hr. 
          rewrite /XMSS_INDEX_BYTES W64toBytes_truncateu32 //=; first by smt(@W32 pow2_32).
          do congr.
 
seq 1 1 : (  
    #{/~0 <= to_uint sk{2}.`Types.idx}
     {/~to_uint sk{2}.`Types.idx < 1048575}
     {/~idx{2} = sk{2}.`Types.idx}
     {/~to_uint idx{1} = to_uint sk{2}.`Types.idx}
     {/~to_list idx_bytes{1} = EncodeIdx sk{2}.`Types.idx}pre /\
     
     1 <= to_uint sk{2}.`Types.idx /\
       to_uint sk{2}.`Types.idx <= 1048575 /\ 

     idx{2} = sk{2}.`Types.idx - W32.one /\
     to_uint idx{1} = to_uint sk{2}.`Types.idx - 1 /\

     to_list idx_bytes{1} = EncodeIdx (sk{2}.`Types.idx - W32.one)
).
    + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25.
      do split; first last.
         - smt(@W32 pow2_32).
         - smt(@W32 pow2_32).
         - ring.
         - smt(@W32 pow2_32).
         - by rewrite H20; congr; ring.
         - rewrite tP => j?.
           rewrite initiE //=.        
           case (0 <= j < 3) => ?.
              * rewrite (: aux_0{1}.[j] = nth witness (to_list aux_0{1}) j) 1:/# H25.
                rewrite /DecodeSkNoOID get_of_list // => />.
                rewrite nth_cat !size_cat size_EncodeIdx /XMSS_INDEX_BYTES !valP n_val /= ifT 1:/#.
                rewrite nth_cat !size_cat size_EncodeIdx /XMSS_INDEX_BYTES !valP n_val /= ifT 1:/#.
                rewrite nth_cat !size_cat size_EncodeIdx /XMSS_INDEX_BYTES !valP n_val /= ifT 1:/#.
                rewrite nth_cat size_EncodeIdx /XMSS_INDEX_BYTES ifT 1:/#.
                reflexivity.
              * rewrite /DecodeSkNoOID get_of_list // => />.
                rewrite get_of_list //. 
                case (3 <= j < 3 + n) => ?.
                  - rewrite nth_cat !size_cat size_EncodeIdx /XMSS_INDEX_BYTES !valP n_val /= ifT 1:/#.
                    rewrite nth_cat !size_cat size_EncodeIdx /XMSS_INDEX_BYTES !valP n_val /= ifT 1:/#.
                    rewrite nth_cat !size_cat size_EncodeIdx /XMSS_INDEX_BYTES !valP n_val /= ifT 1:/#.
                    rewrite nth_cat size_EncodeIdx /XMSS_INDEX_BYTES ifF 1:/#.
                    rewrite nth_cat !size_cat size_EncodeIdx /XMSS_INDEX_BYTES !valP n_val /= ifT 1:/#.
                    rewrite nth_cat !size_cat size_EncodeIdx /XMSS_INDEX_BYTES !valP n_val /= ifT 1:/#.
                    rewrite nth_cat !size_cat size_EncodeIdx /XMSS_INDEX_BYTES !valP n_val /= ifT 1:/#.
                    rewrite nth_cat size_EncodeIdx /XMSS_INDEX_BYTES ifF 1:/#.
                    reflexivity.
                case (3 <= j < 3 + n + n ) => ?.
                  - rewrite nth_cat !size_cat size_EncodeIdx /XMSS_INDEX_BYTES !valP n_val /= ifT 1:/#.
                    rewrite nth_cat !size_cat size_EncodeIdx /XMSS_INDEX_BYTES !valP n_val /= ifT 1:/#.
                    rewrite nth_cat !size_cat size_EncodeIdx /XMSS_INDEX_BYTES !valP n_val /= ifF 1:/#.
                    rewrite nth_cat !size_cat size_EncodeIdx /XMSS_INDEX_BYTES !valP n_val /= ifT 1:/#.
                    rewrite nth_cat !size_cat size_EncodeIdx /XMSS_INDEX_BYTES !valP n_val /= ifT 1:/#.
                    rewrite nth_cat !size_cat size_EncodeIdx /XMSS_INDEX_BYTES !valP n_val /= ifF 1:/#.                   
                    reflexivity.
                case (3 <= j < 3 + n + n + n) => ?.
                  - rewrite nth_cat !size_cat size_EncodeIdx /XMSS_INDEX_BYTES !valP n_val /= ifT 1:/#.
                    rewrite nth_cat !size_cat size_EncodeIdx /XMSS_INDEX_BYTES !valP n_val /= ifF 1:/#.
                    rewrite nth_cat !size_cat size_EncodeIdx /XMSS_INDEX_BYTES !valP n_val /= ifT 1:/#.
                    rewrite nth_cat !size_cat size_EncodeIdx /XMSS_INDEX_BYTES !valP n_val /= ifF 1:/#.
                    reflexivity.
                rewrite nth_cat !size_cat size_EncodeIdx /XMSS_INDEX_BYTES !valP n_val /= ifF 1:/#.
                rewrite nth_cat !size_cat size_EncodeIdx /XMSS_INDEX_BYTES !valP n_val /= ifF 1:/#.
                reflexivity.

seq 1 1 : (
    #pre /\ 
    to_list index_bytes{1} = val idx_bytes{2} /\
    to_list index_bytes{1} = toByte idx{2} n
).
    + ecall {1} (ull_to_bytes_32_correct idx{1}).
      auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25*.
      do split; 1,2: by smt().
      move => ?? result ->.
      split; last first.
         *  apply (eq_from_nth witness); first by rewrite /toByte size_rev size_mkseq size_rev size_mkseq /#.
            rewrite size_W64toBytes_ext // => j?.
            rewrite toByte_32_64 1:/#.
            congr.
            rewrite -toByte_32_64 1:/# n_val.
            apply (eq_from_nth witness); rewrite ?size_toByte_32 // size_W64toBytes_ext // => i?.
            have ?: 0 <= to_uint idx{1} < W32.max_uint by smt().
            congr.
            rewrite (nth_toByte_W64toBytes (sk{2}.`Types.idx - W32.one) idx{1}) // H24.
            smt(@W32 pow2_32).
      apply (eq_from_nth witness); first by rewrite valP n_val /toByte size_rev size_mkseq 1:/# /#. 
      rewrite size_W64toBytes_ext // => j?.
      rewrite insubdK; first by rewrite /P size_rev size_mkseq /#.
      rewrite toByte_32_64 1:/#.
      congr.
      rewrite -toByte_32_64 1:/# n_val.
      apply (eq_from_nth witness); rewrite ?size_toByte_32 // size_W64toBytes_ext // => i?.
      have ?: 0 <= to_uint idx{1} < W32.max_uint by smt().
      congr.
      rewrite (nth_toByte_W64toBytes (sk{2}.`Types.idx - W32.one) idx{1}) // H24.
      smt(@W32 pow2_32).
 

seq 1 0 : (
    #pre /\ 
    to_list sk_prf{1} = val sk_prf{2}
).
    + auto => /> &1 &2 *; apply (eq_from_nth witness); rewrite ?valP ?n_val size_to_list // => j?.
      rewrite get_to_list initiE 1:/# /= /DecodeSkNoOID get_of_list 1:/#.
      rewrite nth_cat !size_cat size_EncodeIdx /XMSS_INDEX_BYTES !valP n_val /= ifT 1:/#.
      rewrite nth_cat !size_cat size_EncodeIdx /XMSS_INDEX_BYTES !valP n_val /= ifT 1:/#.
      rewrite nth_cat !size_cat size_EncodeIdx /XMSS_INDEX_BYTES !valP n_val /= ifF 1:/#.
      reflexivity.

seq 1 1 : (
    #pre /\ 
    to_list buf{1} = val _R{2}
).
    + inline {1} M(Syscall).__prf_ M(Syscall)._prf; wp; sp; conseq />.      
      exists * in_00{1}, key0{1}; elim * => _P1 _P2.
      call {1} (prf_correctness _P1 _P2) => [/# |].  
      auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28.
      do split; first by smt(@NBytes).
          - apply nbytes_eq.
            rewrite insubdK; first by rewrite /P size_to_list /#.
            apply (eq_from_nth witness); first by rewrite valP n_val size_to_list.
            rewrite valP n_val => j?.
            by rewrite H28.
          - by move => ????->.
 
seq 1 0 : (#pre /\ sub signature{1} XMSS_INDEX_BYTES n = val _R{2}).
    + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 <-.
      split.
         * rewrite /XMSS_INDEX_BYTES.
           apply (eq_from_nth witness); first by rewrite size_sub // size_to_list. 
           rewrite size_sub // => i?. 
           by rewrite -H18 !nth_sub //= initiE 1:/# /= ifF 1:/#.
         * apply (eq_from_nth witness); first by rewrite size_to_list size_sub n_val.
           rewrite size_sub n_val // => j?.
           by rewrite nth_sub // initiE 1:/# /= ifT 1:/# /copy_8 /XMSS_INDEX_BYTES.
 
seq 1 0 : (
    #pre /\ 
    to_list pub_root{1} = val root{2} 
).
    + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 *.
      apply (eq_from_nth witness); first by rewrite size_to_list valP n_val.
      rewrite size_to_list => i?.
      rewrite get_to_list initiE //=. 
      rewrite /DecodeSkNoOID get_of_list 1:/#.
      rewrite nth_cat !size_cat size_EncodeIdx /XMSS_INDEX_BYTES !valP n_val ifT 1:/#.
      rewrite nth_cat !size_cat size_EncodeIdx /XMSS_INDEX_BYTES !valP n_val ifF 1:/#.
      congr; ring.
 
outline {2} [1-2] { 
    _M' <@ M_Hash.hash (
          (insubd (val _R ++ val root ++ val idx_bytes))%TheeNBytes, 
          m); 
}.
 
seq 2 0 : (
    #{/~to_uint t64{1} = to_uint idx_new{2}}
     {/~truncateu32 t64{1} = idx{2} + W32.one}pre /\
    to_uint t64{1} = to_uint sm_ptr{1} + (XMSS_SIG_BYTES - 128)
); first by auto => /> *; rewrite to_uintD_small of_uintK 1:/# /= /XMSS_SIG_BYTES.
 
conseq  ( :
sk{1} = DecodeSkNoOID sk{2} /\
m{2} = load_buf Glob.mem{1} m_ptr{1} (to_uint mlen{1}) /\
_sm_ptr = sm_ptr{1} /\

0 < to_uint mlen{1} < 18446744073709551615 /\
0 <= to_uint sm_ptr{1} + XMSS_SIG_BYTES < 18446744073709551615 /\
0 <= to_uint sm_ptr{1} + XMSS_SIG_BYTES + to_uint mlen{1} < 18446744073709551615 /\
0 <= to_uint m_ptr{1} + to_uint mlen{1} < 18446744073709551615 /\
0 <= to_uint m_ptr{1} < 18446744073709551615 /\
0 <= to_uint smlen_ptr{1} < W64.max_uint /\
0 <= to_uint smlen_ptr{1} + 8 < W64.max_uint /\

disjoint_ptr (to_uint sm_ptr{1}) (XMSS_SIG_BYTES + to_uint mlen{1})
             (to_uint m_ptr{1}) (to_uint mlen{1}) /\

disjoint_ptr (to_uint sm_ptr{1}) (XMSS_SIG_BYTES + to_uint mlen{1})
             (to_uint smlen_ptr{1}) 8 /\

disjoint_ptr (to_uint smlen_ptr{1}) 8 (to_uint m_ptr{1}) (to_uint mlen{1}) /\

ots_addr{1} = zero_addr /\
address{2} = ots_addr{1} /\

root{2} = sk{2}.`sk_root /\
sk_prf{2} = sk{2}.`Types.sk_prf /\
idx_new{2} = idx{2} + W32.one /\
load_buf Glob.mem{1} (sm_ptr{1} + (of_int 4963)%W64) (to_uint mlen{1}) = m{2} /\ (* Esta parte pode estar mal *)

(* Idx Bytes *)
sub signature{1} 0 XMSS_INDEX_BYTES = to_list idx_bytes{1} /\
to_list idx_bytes{1} = EncodeIdx (sk{2}.`Types.idx - W32.one) /\
to_list aux_0{1} = EncodeIdx idx_new{2} /\
1 <= to_uint sk{2}.`Types.idx <= 1048575 /\
idx{2} = sk{2}.`Types.idx - W32.one /\
to_uint idx{1} = to_uint sk{2}.`Types.idx - 1 /\
to_list index_bytes{1} = val idx_bytes{2} /\
to_list index_bytes{1} = toByte idx{2} n /\

to_list sk_prf{1} = val sk_prf{2} /\
to_list buf{1} = val _R{2} /\
sub signature{1} XMSS_INDEX_BYTES n = val _R{2} /\
to_list pub_root{1} = val root{2} /\

to_uint t64{1} = to_uint sm_ptr{1} + (XMSS_SIG_BYTES - 128)

             ==> _
); first by auto.
 
seq 1 1 : (
  sk{1} = DecodeSkNoOID sk{2} /\
(*  m{2} = load_buf Glob.mem{1} m_ptr{1} (to_uint mlen{1}) /\ *)
  _sm_ptr = sm_ptr{1} /\
  (0 < to_uint mlen{1} && to_uint mlen{1} < 18446744073709551615) /\
  (0 <= to_uint sm_ptr{1} + XMSS_SIG_BYTES &&
   to_uint sm_ptr{1} + XMSS_SIG_BYTES < 18446744073709551615) /\
  (0 <= to_uint sm_ptr{1} + XMSS_SIG_BYTES + to_uint mlen{1} &&
   to_uint sm_ptr{1} + XMSS_SIG_BYTES + to_uint mlen{1} <
   18446744073709551615) /\
  (0 <= to_uint m_ptr{1} + to_uint mlen{1} &&
   to_uint m_ptr{1} + to_uint mlen{1} < 18446744073709551615) /\
  (0 <= to_uint m_ptr{1} && to_uint m_ptr{1} < 18446744073709551615) /\
  (0 <= to_uint smlen_ptr{1} && to_uint smlen_ptr{1} < W64.max_uint) /\
  (0 <= to_uint smlen_ptr{1} + 8 && to_uint smlen_ptr{1} + 8 < W64.max_uint) /\
  disjoint_ptr (to_uint sm_ptr{1}) (XMSS_SIG_BYTES + to_uint mlen{1})
    (to_uint m_ptr{1}) (to_uint mlen{1}) /\
  disjoint_ptr (to_uint sm_ptr{1}) (XMSS_SIG_BYTES + to_uint mlen{1})
    (to_uint smlen_ptr{1}) 8 /\
  disjoint_ptr (to_uint smlen_ptr{1}) 8 (to_uint m_ptr{1}) (to_uint mlen{1}) /\
  ots_addr{1} = zero_addr /\
  address{2} = ots_addr{1} /\
  root{2} = sk{2}.`sk_root /\
  sk_prf{2} = sk{2}.`Types.sk_prf /\
  idx_new{2} = idx{2} + W32.one /\
(*  load_buf Glob.mem{1} (sm_ptr{1} + (of_int 4963)%W64) (to_uint mlen{1}) = m{2} /\ *)
  sub signature{1} 0 XMSS_INDEX_BYTES = to_list idx_bytes{1} /\
  to_list idx_bytes{1} = EncodeIdx (sk{2}.`Types.idx - W32.one) /\
  to_list aux_0{1} = EncodeIdx idx_new{2} /\
  (1 <= to_uint sk{2}.`Types.idx && to_uint sk{2}.`Types.idx <= 1048575) /\
  idx{2} = sk{2}.`Types.idx - W32.one /\
  to_uint idx{1} = to_uint sk{2}.`Types.idx - 1 /\
  to_list index_bytes{1} = val idx_bytes{2} /\
  to_list index_bytes{1} = toByte idx{2} n /\
  to_list sk_prf{1} = val sk_prf{2} /\
  to_list buf{1} = val _R{2} /\
  sub signature{1} XMSS_INDEX_BYTES n = val _R{2} /\
  to_list pub_root{1} = val root{2} /\
(* to_uint t64{1} = to_uint sm_ptr{1} + (XMSS_SIG_BYTES - 128) /\ *) 

  to_list mhash{1} = val _M'{2} (* OBS: a partir daqui, o q ta em memoria nao me interessa *) /\

  address{2} = ots_addr{1} (* esqueci me disto *)
).
    + exists * Glob.mem{1}, 
               (init (fun (i_0 : int) => signature{1}.[3 + i_0]))%Array32,
               pub_root{1},
               idx{1},
               t64{1},
               mlen{1}.
      elim * => P0 P1 P2 P3 P4 P5.
      call (hash_message_correct P0 P1 P2 P3 P4 P5) => [/# |].
      auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30.
      do split.
         * smt(@W64 pow2_64).
         * smt().
         * move => ?; rewrite /XMSS_FULL_HEIGHT /= /#.
         * apply three_nbytes_eq; rewrite !insubdK.
              - rewrite /P !size_cat !valP /#.
              - rewrite /P !size_cat !size_to_list size_toByte_64 /#. 
              - rewrite H29.
           do congr.
              - rewrite -H27 /XMSS_INDEX_BYTES; apply (eq_from_nth witness); rewrite // ?size_to_list // => j?.
                rewrite H27 get_to_list initiE //=. 
                have ->: signature{1}.[3 + j] = nth witness (sub signature{1} XMSS_INDEX_BYTES n) j by rewrite nth_sub /#.
                by rewrite H28.
              - apply (eq_from_nth witness); rewrite valP n_val ?size_toByte_64 // => j?.
                rewrite -H24 H25.
                rewrite toByte_32_64 1:/#.
                rewrite -W64toBytes_ext_toByte_64; congr; congr.
                rewrite wordP => k?.
                rewrite !get_to_uint to_uint_zeroextu64 H23 (: (0 <= k < 64) = true) 1:/# /=.
                congr; smt(@W32 @W64 pow2_32 pow2_64).

         * apply (eq_from_nth witness); rewrite !size_load_buf //; 1,2,3: by smt().
           move => j?; rewrite !nth_load_buf //. 
           have ->: to_uint (P4 + (of_int 128)%W64) = to_uint P4 + 128 by smt(@W64 pow2_64).
           rewrite H30 /XMSS_SIG_BYTES /=.
           have ->: P0.[to_uint m_ptr{1} + j] = nth witness (load_buf P0 m_ptr{1} (to_uint P5)) j by rewrite nth_load_buf /#.
           rewrite -H17 nth_load_buf //; do congr; smt(@W64 pow2_64).

swap {2} 3 -2.
seq 2 1 : #pre.
    + inline {1}; auto => /> *; smt(zero_addr_setZero).

seq 2 1 : (#pre /\ to_uint idx_tree{1} = to_uint idx_tree{2}).
    + auto => /> *; rewrite to_uint_shr of_uintK //= h_val d_val /= to_uint_shr //=; smt(@W32 pow2_32).

seq 2 1 : (
    #pre /\ 
    ={idx_leaf} /\
    0 <= to_uint idx_leaf{1} < 2 ^ 20
).
    + auto => /> *; do split.
        - rewrite and_comm ; congr; [by rewrite /truncateu32; smt(@W32 pow2_32) | by rewrite /(`<<`) /= h_val d_val /=].
        - rewrite /(`<<`) /=; smt(@W32 pow2_32).
        - rewrite /(`<<`) /=; smt(@W32 pow2_32).

seq 1 1 : (#{/~ots_addr{1} = zero_addr}pre /\ ots_addr{1}.[4] = W32.zero).
    + inline; auto => /> *; split; last first.
          * rewrite /set_tree_addr tP => j?; rewrite !get_setE //.
            case (j = 1) => [-> | ?].
               - rewrite ifF 1:/# ifF 1:/# (: 63 = 2^6 - 1) 1:/# and_mod //=.
                 rewrite /truncateu32; congr. 
                 rewrite /truncateu8 of_uintK /=.
                 rewrite to_uint_shr of_uintK //= /#.
            case (j = 2) => [? | ?]; last by smt(zero_addr_i).
            rewrite /truncateu32; congr => /=; smt(@W32 pow2_32).
      rewrite /set_tree_addr tP => j?.
      rewrite !get_setE //.
      case (j = 1) => [-> /= | ?].
        - rewrite /truncateu32; congr.
          rewrite to_uint_shr /truncateu8 !of_uintK (: 63 = 2^6 - 1) 1..3:/# and_mod // !of_uintK /#.
      case (j = 2) => [| ?]; [smt(@W32 pow2_32) | smt(sub_k)].
 
seq 1 1 : (
  #pre /\
  sub aux_2{1} 0 3 = sub ots_addr{1} 0 3 /\
  to_list aux_1{1} = 
    DecodeWotsSignature_List sig_tmp{2} ++ DecodeAuthPath_List auth{2}
).
    + inline {1} 1; wp; conseq />.
      exists * mhash{1}, sk{2}, idx_leaf{1}, ots_addr{1}, address{2}.
      elim * => P0 P1 P2 P3 P4.
      call (treesig_correct P0 P1 P2 P3 P4) => [/# |].
      auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33.
      do split. 
        - rewrite H29; smt(@NBytes).
        - move => ?? result Hr.
          apply (eq_from_nth witness). 
             * rewrite size_to_list size_cat size_DecodeWotsSignature_List size_DecodeAuthPath_List /#.
          rewrite size_to_list => j?; rewrite get_to_list nth_cat size_DecodeWotsSignature_List.
          case (0 <= j < n * len) => [Hfst | Hsnd]; [rewrite ifT 1:/# | rewrite ifF 1:/#].
             * rewrite /DecodeWotsSignature_List /EncodeWotsSignature.
               rewrite nth_nbytes_flatten; first by rewrite valP /#.
               rewrite /EncodeReducedSignature => />.
               rewrite /EncodeWotsSignatureList insubdK.
                  + rewrite /P size_map size_chunk 1:/# size_sub_list /#.
               rewrite (nth_map witness). 
                  + rewrite size_chunk 1:/# size_sub_list /#.
               rewrite insubdK.
                  + rewrite /P nth_chunk 1:/#; first by rewrite size_sub_list /#.
                    rewrite size_take 1:/# size_drop 1:/# size_sub_list /#.
               rewrite nth_chunk 1:/#; first by rewrite size_sub_list /#.
               rewrite nth_take 1..2:/# nth_drop 1..2:/# nth_sub_list 1:/#.
               rewrite get_to_list /=; congr; smt().
             * rewrite /DecodeWotsSignature_List /EncodeWotsSignature.
               rewrite nth_nbytes_flatten; first by rewrite valP /#.
               rewrite /EncodeReducedSignature => />.
               rewrite /EncodeWotsSignatureList insubdK.
                  + rewrite /P size_map size_chunk 1:/# size_sub_list /#.
               rewrite (nth_map witness). 
                  + rewrite size_chunk 1:/# size_sub_list /#.
               rewrite insubdK.
                  + rewrite /P nth_chunk 1:/#; first by rewrite size_sub_list /#.
                    rewrite size_take 1:/# size_drop 1:/# size_sub_list /#.
               rewrite nth_chunk 1:/#; first by rewrite size_sub_list /#.
               rewrite nth_take 1..2:/# nth_drop 1..2:/# nth_sub_list 1:/#.
               rewrite get_to_list /=; congr; smt().
  
seq 1 0 : (
    #pre /\ 
    sub signature{1} (XMSS_INDEX_BYTES + n) XMSS_REDUCED_SIG_BYTES = 
       DecodeWotsSignature_List sig_tmp{2} ++ DecodeAuthPath_List auth{2}
).
    + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35.
      do split.
         - apply (eq_from_nth witness); first by rewrite size_to_list size_sub /#.
           rewrite /XMSS_INDEX_BYTES size_sub // => j?.
           rewrite nth_sub // initiE 1:/# /= ifF 1:/#.
           have ->: signature{1}.[j] = nth witness (sub signature{1} 0 XMSS_INDEX_BYTES) j by rewrite nth_sub /#.
           by rewrite H17 get_to_list.
         - apply (eq_from_nth witness); first by rewrite valP size_sub /#.
           rewrite n_val size_sub // => j?.
           rewrite nth_sub // initiE 1:/# /= ifF 1:/#. 
           rewrite -H27 nth_sub /#.

         - apply (eq_from_nth witness). 
            + rewrite size_cat size_DecodeWotsSignature_List size_DecodeAuthPath_List size_sub /#.
           rewrite size_sub // => j?.
           rewrite nth_sub //= initiE 1:/# /= ifT 1:/#.
           rewrite -get_to_list H35 /#.

seq 0 1 : (
  #pre /\ 
  sig{2}.`sig_idx = idx_leaf{2} /\
  sig{2}.`r = _R{2} /\
  sig{2}.`r_sigs = [EncodeReducedSignature (sub signature{1} (XMSS_INDEX_BYTES + n) XMSS_REDUCED_SIG_BYTES)]
).
    + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 H36.
      rewrite /EncodeReducedSignature; congr; [apply len_n_bytes_eq | apply  auth_path_eq].
        - apply (eq_from_nth witness); first by rewrite !valP.
          rewrite valP len_val => j?.
          rewrite H36.
          apply nbytes_eq; apply (eq_from_nth witness); first by rewrite !NBytes.valP. 
          rewrite valP n_val => k?.
          rewrite /EncodeWotsSignatureList insubdK.
             * rewrite /P size_map size_chunk // size_sub_list // /#. 
          rewrite (nth_map witness); first by rewrite size_chunk // size_sub_list // /#.
          rewrite insubdK.
             * rewrite /P /chunk nth_mkseq /=; first by rewrite size_sub_list /#. 
               rewrite size_take 1:/# size_drop 1:/# size_sub_list /#.
          rewrite nth_chunk 1:/#. 
             * rewrite size_sub_list /#.
          rewrite nth_take 1,2:/# nth_drop 1,2:/#.
          rewrite nth_sub_list 1:/# nth_cat size_DecodeWotsSignature_List ifT 1:/#.
          rewrite /DecodeWotsSignature_List nth_nbytes_flatten 2:/# valP /#. 
        - apply (eq_from_nth witness); first by rewrite !valP.
          rewrite valP h_val d_val /= => j?.
          rewrite H36.
          apply nbytes_eq; apply (eq_from_nth witness); first by rewrite !NBytes.valP. 
          rewrite valP n_val => k?.
          rewrite /EncodeWotsSignatureList insubdK.
             * rewrite /P size_map size_chunk 1:/# size_sub_list // /#. 
          rewrite (nth_map witness); first by rewrite size_chunk 1:/# size_sub_list /#.
          rewrite insubdK.
             * rewrite /P /chunk nth_mkseq /=; first by rewrite size_sub_list /#. 
               rewrite size_take 1:/# size_drop 1:/# size_sub_list /#.
          rewrite nth_chunk 1:/#. 
             * rewrite size_sub_list /#.
          rewrite nth_take 1,2:/# nth_drop 1,2:/#.
          rewrite nth_sub_list 1:/# nth_cat size_DecodeWotsSignature_List ifF 1:/#.
          rewrite /DecodeWotsSignature_List nth_nbytes_flatten 2:/# valP /#. 

seq 1 0 : (
  #{/~address{2} = ots_addr{1}}
   {/~ots_addr{1}.[4] = W32.zero}pre /\
   sub ots_addr{1} 0 3 = sub address{2} 0 3
 ); first by auto.

while (sk{1} = DecodeSkNoOID sk{2} /\
_sm_ptr = sm_ptr{1} /\

0 < to_uint mlen{1} < 18446744073709551615 /\

0 <= to_uint sm_ptr{1} + XMSS_SIG_BYTES < 18446744073709551615 /\

0 <= to_uint sm_ptr{1} + XMSS_SIG_BYTES + to_uint mlen{1} < 18446744073709551615 /\
0 <= to_uint m_ptr{1} + to_uint mlen{1} < 18446744073709551615 /\
0 <= to_uint m_ptr{1} < 18446744073709551615 /\
0 <= to_uint smlen_ptr{1} < W64.max_uint /\
0 <= to_uint smlen_ptr{1} + 8 < W64.max_uint /\

disjoint_ptr (to_uint sm_ptr{1}) (XMSS_SIG_BYTES + to_uint mlen{1})
  (to_uint m_ptr{1}) (to_uint mlen{1}) /\
disjoint_ptr (to_uint sm_ptr{1}) (XMSS_SIG_BYTES + to_uint mlen{1})
  (to_uint smlen_ptr{1}) 8 /\
disjoint_ptr (to_uint smlen_ptr{1}) 8 (to_uint m_ptr{1}) (to_uint mlen{1}) /\

sk_prf{2} = sk{2}.`Types.sk_prf /\
idx_new{2} = idx{2} + W32.one /\

sub signature{1} 0 XMSS_INDEX_BYTES = to_list idx_bytes{1} /\

to_list idx_bytes{1} = EncodeIdx (sk{2}.`Types.idx - W32.one) /\

1 <= to_uint sk{2}.`Types.idx <= 1048575 /\
idx{2} = sk{2}.`Types.idx - W32.one /\
to_uint idx{1} = to_uint sk{2}.`Types.idx - 1 /\
to_list index_bytes{1} = val idx_bytes{2} /\
to_list index_bytes{1} = toByte idx{2} n /\
to_list sk_prf{1} = val sk_prf{2} /\
sub signature{1} XMSS_INDEX_BYTES n = val _R{2} /\
to_uint idx_tree{1} = to_uint idx_tree{2} /\
={idx_leaf} /\
0 <= to_uint idx_leaf{1} < 2 ^ 20 /\

sig{2}.`XMSS_MT_Types.r = _R{2} /\
(* sig{2}.`sig_idx = idx_leaf{2} /\ *)

(forall (k : int), 0 <= k < size (sig{2}.`r_sigs) =>
nth witness (sig{2}.`r_sigs) k = 
  EncodeReducedSignature (
      sub signature{1} (XMSS_INDEX_BYTES + n) (i{1} * XMSS_REDUCED_SIG_BYTES)
)) /\

1 <= j{2} <= 2 /\ i{1} = j{2} /\
((1 < i{1}) => to_list root{1} = val root{2}) /\
size (sig{2}.`r_sigs) = j{2}  /\

  sub ots_addr{1} 0 3 = sub address{2} 0 3
); last by admit.

seq 2 0 : (
  #pre /\
  to_list sk_seed{1} = val sk{2}.`Types.sk_seed /\
  to_list pub_seed{1} = val sk{2}.`Types.pub_seed_sk
).
    + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35.
      do split; apply (eq_from_nth witness); rewrite size_to_list ?valP ?n_val // => j?; rewrite get_to_list initiE //= /DecodeSkNoOID get_of_list => />; 1,3: by smt().
          - rewrite nth_cat !size_cat !valP n_val size_EncodeIdx /XMSS_INDEX_BYTES ifT 1:/#.
            rewrite nth_cat !size_cat !valP n_val size_EncodeIdx /XMSS_INDEX_BYTES ifT 1:/#.  
            rewrite nth_cat !size_cat !valP n_val size_EncodeIdx /XMSS_INDEX_BYTES ifT 1:/#.
            rewrite nth_cat size_EncodeIdx /XMSS_INDEX_BYTES ifF 1:/#.
            by [].
          - rewrite nth_cat !size_cat !valP n_val size_EncodeIdx /XMSS_INDEX_BYTES ifF 1:/#.
            by [].

seq 1 0 : (#pre /\ ots_addr{1}.[4] = W32.zero).
    + auto => /> *; apply (eq_from_nth witness); rewrite !size_sub // => j?; rewrite !nth_sub // !get_setE //=.
      case (j = 4) => [/# |]; smt(sub_k).

seq 1 1 : (
  #pre /\ 
  to_list root{1} = val root{2}
).
    + inline {1} 1; inline {1} 13.
      wp; conseq />.
      sp.
      exists * sk_seed1{1}, pub_seed1{1}, s0{1}, t0{1}, subtree_addr0{1}, address{2}.
      elim * => P0 P1 P2 P3 P4 P5.
      call (treehash_correct P0 P1 P2 P3 P4 P5) => [/# |].
      auto => /> &1 &2 *; do split; 1,2: by smt(@NBytes).
      smt().

seq 1 1 : #pre.
    + auto => /> *.
      rewrite h_val d_val /= to_uint_shr of_uintK //=.
      rewrite to_uint_shr //= /#. 
 
seq 2 1 : #pre.
    + auto => /> *.
      rewrite h_val d_val /=.
      do split.
       - rewrite and_comm; congr; first by smt(@W32 pow2_32).
         by rewrite /(`<<`) /=.
       - rewrite /(`<<`) /=; smt(@W32 pow2_32).
       - move => ?; rewrite /(`<<`) /=; smt(@W32 pow2_32).

seq 2 2 : #pre.
    + inline {1}; auto => /> *; rewrite /set_ots_addr /set_tree_addr /set_layer_addr.
      apply (eq_from_nth witness); rewrite !size_sub // => j?; rewrite !nth_sub // !get_setE //=.
       case (j = 0) => ?.
          * rewrite !ifF 1..4:/#; reflexivity.
       case (j = 1) => ?.
          * rewrite !ifF 1,2:/# (: 63 = 2^6 - 1) 1:/# and_mod //= /truncateu8 of_uintK /=.
            rewrite /truncateu32 to_uint_shr of_uintK //=; congr; smt().
      case (j = 2) => ?; last by smt().
      rewrite /truncateu32; congr; smt(@W32 pow2_32).
seq 1 1 : (
  #pre /\
  sub aux_2{1} 0 3 = sub ots_addr{1} 0 3 /\
  to_list aux_1{1} = 
    DecodeWotsSignature_List sig_tmp{2} ++ DecodeAuthPath_List auth{2}
).
    + inline {1} 1; wp; conseq />.
      exists * root{1}, sk{2}, idx_leaf{1}, ots_addr{1}, address{2}.
      elim * => P0 P1 P2 P3 P4.
      call (treesig_correct P0 P1 P2 P3 P4) => [/# |].
      auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 H36 H37 H38 H39.
      split; first by smt(@NBytes).
      move => ?? resL Hr0.
          apply (eq_from_nth witness). 
             * rewrite size_to_list size_cat size_DecodeWotsSignature_List size_DecodeAuthPath_List /#.
          rewrite size_to_list => j?; rewrite get_to_list nth_cat size_DecodeWotsSignature_List.
          case (0 <= j < n * len) => [Hfst | Hsnd]; [rewrite ifT 1:/# | rewrite ifF 1:/#].
             * rewrite /DecodeWotsSignature_List /EncodeWotsSignature.
               rewrite nth_nbytes_flatten; first by rewrite valP /#.
               rewrite /EncodeReducedSignature => />.
               rewrite /EncodeWotsSignatureList insubdK.
                  + rewrite /P size_map size_chunk 1:/# size_sub_list /#.
               rewrite (nth_map witness). 
                  + rewrite size_chunk 1:/# size_sub_list /#.
               rewrite insubdK.
                  + rewrite /P nth_chunk 1:/#; first by rewrite size_sub_list /#.
                    rewrite size_take 1:/# size_drop 1:/# size_sub_list /#.
               rewrite nth_chunk 1:/#; first by rewrite size_sub_list /#.
               rewrite nth_take 1..2:/# nth_drop 1..2:/# nth_sub_list 1:/#.
               rewrite get_to_list /=; congr; smt().
             * rewrite /DecodeWotsSignature_List /EncodeWotsSignature.
               rewrite nth_nbytes_flatten; first by rewrite valP /#.
               rewrite /EncodeReducedSignature => />.
               rewrite /EncodeWotsSignatureList insubdK.
                  + rewrite /P size_map size_chunk 1:/# size_sub_list /#.
               rewrite (nth_map witness). 
                  + rewrite size_chunk 1:/# size_sub_list /#.
               rewrite insubdK.
                  + rewrite /P nth_chunk 1:/#; first by rewrite size_sub_list /#.
                    rewrite size_take 1:/# size_drop 1:/# size_sub_list /#.
               rewrite nth_chunk 1:/#; first by rewrite size_sub_list /#.
               rewrite nth_take 1..2:/# nth_drop 1..2:/# nth_sub_list 1:/#.
               rewrite get_to_list /=; congr; smt().

auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 H40 H41.
do split; admit. 
