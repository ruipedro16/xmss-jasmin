pragma Goals : printall.

require import AllCore List RealExp IntDiv Distr DList IntDiv.
from Jasmin require import JModel JArray.

require import Params Address Types Hash LTree XMSS_MT_PRF XMSS_MT_Types XMSS_MT_Params.
require import XMSS_IMPL Parameters.

require import Repr2. 
require import Utils2.

require import Array3 Array8 Array32 Array64 Array68 Array96 Array131 Array352.
require import Array2144 Array2464 Array4963.
require import WArray32 WArray96 WArray131.

require import Correctness_Address Correctness_Bytes Correctness_Mem Correctness_Hash.
require import DistrUtils.

lemma load_store_W64 (mem : global_mem_t) (a : address) (v : W64.t) :
    loadW64 (storeW64 mem a v) a = v.
proof.
rewrite /loadW64 /storeW64 wordP => j?.
rewrite pack8E /stores initiE // => />. 
rewrite initiE 1:/# => />. 
rewrite get_setE.
  + case (a + j %/ 8 = a + 7) => *; [rewrite /(\bits8) initiE /# |].
rewrite get_setE.
  + case (a + j %/ 8 = a + 6) => *; [rewrite /(\bits8) initiE /# |].
rewrite get_setE.
  + case (a + j %/ 8 = a + 5) => *; [rewrite /(\bits8) initiE /# |].
rewrite get_setE.
  + case (a + j %/ 8 = a + 4) => *; [rewrite /(\bits8) initiE /# |].
rewrite get_setE.
  + case (a + j %/ 8 = a + 3) => *; [rewrite /(\bits8) initiE /# |].
rewrite get_setE.
  + case (a + j %/ 8 = a + 2) => *; [rewrite /(\bits8) initiE /# |].
rewrite get_setE.
  + case (a + j %/ 8 = a + 1) => *; [rewrite /(\bits8) initiE /# |].
rewrite get_setE.
  + rewrite ifT 1:/# /(\bits8) initiE /#.
qed.

(** 
  This lemma asserts that two memory regions specified by their starting addresses and lengths are disjoint.
  
  Parameters:
  - p1 : int - The starting address of the first memory region.
  - l1 : int - The length of the first memory region.
  - p2 : int - The starting address of the second memory region.
  - l2 : int - The length of the second memory region.

  The lemma states that for all indices `k1` and `k2` within the bounds of their respective memory regions,
  the addresses `p1 + k1` and `p2 + k2` do not overlap, i.e., they are not equal.
**)
pred disjoint_ptr (p1 l1 p2 l2 : int) =
  forall (k1 : int), 0 <= k1 < l1 =>
    forall (k2 : int), 0 <= k2 < l2 =>
      p1 + k1 <> p2 + k2.

lemma disjoint_ptr_comm (p1 l1 p2 l2 : int) : 
    disjoint_ptr p1 l1 p2 l2 <=>
    disjoint_ptr p2 l2 p1 l1 by smt().

(**

  This lemma asserts that if two memory regions specified by their starting addresses and lengths are disjoint, 
  then any subregion of the second memory region is also disjoint from the first memory region.
  
  Parameters:
  - p1 : int - The starting address of the first memory region.
  - l1 : int - The length of the first memory region.
  - p2 : int - The starting address of the second memory region.
  - l2 : int - The length of the second memory region.
  - l3 : int - The length of the subregion of the second memory region, such that `l3 < l2`.

**)
lemma disjoint_ptr_sub (p1 l1 p2 l2 l3 : int) :
    disjoint_ptr p1 l1 p2 l2 =>
    l3 < l2 =>
    disjoint_ptr p1 l1 p2 l3 by smt().

lemma sign_correct (_sk : xmss_sk, _sm_ptr _smlen_ptr _m_ptr _mlen : W64.t) :
    n = XMSS_N /\ 
    d = XMSS_D /\
    h = XMSS_FULL_HEIGHT /\
    prf_padding_val = XMSS_HASH_PADDING_PRF /\ 
    padding_len = XMSS_PADDING_LEN /\
    H_msg_padding_val = XMSS_HASH_PADDING_HASH =>
    equiv [
      M(Syscall).__xmssmt_core_sign ~ XMSS_MT_PRF.sign :

      arg{1}.`1 = DecodeSkNoOID _sk /\
      arg{1}.`2 = _sm_ptr /\
      arg{1}.`3 = _smlen_ptr /\
      arg{1}.`4 = _m_ptr /\
      arg{1}.`5 = _mlen  /\

      arg{2}.`1 =_sk /\
      arg{2}.`2 = load_buf Glob.mem{1} _m_ptr (to_uint _mlen) /\

      0 <= to_uint _mlen < W64.max_uint /\
      0 <= to_uint _sm_ptr + XMSS_SIG_BYTES < W64.max_uint /\
      0 <= to_uint _sm_ptr + XMSS_SIG_BYTES + to_uint _mlen < W64.max_uint /\
      0 <= to_uint _m_ptr + to_uint _mlen < W64.max_uint /\

      disjoint_ptr (to_uint _sm_ptr) (XMSS_SIG_BYTES + to_uint _mlen) 
                   (to_uint _m_ptr) (to_uint _mlen) /\

      0 <= to_uint sk{2}.`idx < 2^XMSS_FULL_HEIGHT - 1 (* ensures that the maximum number of signatures was not yet reached *)

      ==>
      res{1}.`1 = DecodeSkNoOID res{2}.`2 /\
      res{2}.`1 = EncodeSignature  (load_buf Glob.mem{1} _sm_ptr XMSS_SIG_BYTES)
    ].
proof.
rewrite /XMSS_N /XMSS_D /XMSS_TREE_HEIGHT /XMSS_FULL_HEIGHT => [#] n_val d_val h_val *.
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

(* This copies the message to the end of the signature *)
seq 1 0 : (
    #pre /\
    load_buf Glob.mem{1} (sm_ptr{1} + (of_int XMSS_SIG_BYTES)%W64) (to_uint mlen{1}) =
    load_buf Glob.mem{1} m_ptr{1} (to_uint mlen{1})
).
    + inline; sp; wp.
      while {1} 
      (
        sk{1} = DecodeSkNoOID _sk /\
        smlen_ptr{1} = _smlen_ptr /\
        m_ptr{1} = _m_ptr /\
        mlen{1} = _mlen /\
        sk{2} = _sk /\
        m{2} = load_buf Glob.mem{1} _m_ptr (to_uint _mlen) /\

      disjoint_ptr (to_uint sm_ptr{1}) (XMSS_SIG_BYTES + to_uint mlen{1}) 
                   (to_uint m_ptr{1}) (to_uint mlen{1}) /\

        0 <= to_uint sk{2}.`Types.idx < 1048575 /\
        exit_0{1} = W8.zero /\ 
        ots_addr{1} = zero_addr /\
        
        bytes1{1} = mlen{1} /\
        in_offset1{1} = i0{1} /\
        in_ptr1{1} = m_ptr{1} /\  
        out_offset1{1} = i0{1} + (of_int XMSS_SIG_BYTES)%W64 /\
        out_ptr1{1} = sm_ptr{1} /\

        0 <= to_uint i0{1} <= to_uint mlen{1} /\
        0 <= to_uint mlen{1} < W64.max_uint /\
        0 <= to_uint sm_ptr{1} + XMSS_SIG_BYTES < W64.max_uint /\
        0 <= to_uint sm_ptr{1} + XMSS_SIG_BYTES + to_uint mlen{1} < W64.max_uint /\
        0 <= to_uint m_ptr{1} + to_uint mlen{1} < W64.max_uint /\

       load_buf Glob.mem{1} (sm_ptr{1} + (of_int XMSS_SIG_BYTES)%W64) (to_uint i0{1}) =
       load_buf Glob.mem{1} m_ptr{1} (to_uint i0{1})
        
      )
      (to_uint bytes1{1} - to_uint i0{1}); last first.

         + auto => /> &1 &2 H0 H1 H2 H3 H4 *.
           split; first by apply (eq_from_nth witness); rewrite !size_load_buf /#.
           move => memL i0L. 
           split => [* |]; first by rewrite ultE /#.
           rewrite ultE => H5 H6 H7 H8.
           have ->: to_uint i0L = to_uint _mlen by smt().
           by move => ->.
         + auto => /> &hr H0 H1 H2 H3 H4 H5 H6 H7 H8 H9.
           rewrite ultE => H10 H11 H12 H13 H14.
           do split; 2,3,5: by rewrite to_uintD /#.
             - apply (eq_from_nth witness); first by rewrite !size_load_buf.
               rewrite size_load_buf // => j?.
               rewrite !nth_load_buf // /storeW8 get_setE.
               rewrite ifF //. (* isto e verdade pq os apontadores sao disjuntos *)
               rewrite !to_uintD_small of_uintK 2:/#; 1,2: by smt(@W64 pow2_64). 
               rewrite disjoint_ptr_comm in H0.
               rewrite /disjoint_ptr in H0.
               have ->: (to_uint i0{hr} + XMSS_SIG_BYTES %% W64.modulus) = 
                         to_uint i0{hr} + XMSS_SIG_BYTES
                         by smt(@W64 pow2_64).
               by apply H0; smt().
             - apply (eq_from_nth witness).
                 * rewrite !size_load_buf to_uintD /#.
               rewrite size_load_buf to_uintD_small 1..3:/# /= => j?.
               rewrite !nth_load_buf // /storeW8 get_setE.
               case (j = to_uint i0{hr}) => ?.
                 * rewrite /XMSS_SIG_BYTES ifT.
                      + rewrite !to_uintD_small of_uintK 1,3,5:/#; smt(@W64 pow2_64).
                   rewrite /loadW8 get_setE; smt(@JMemory @W64 pow2_64).
                 * rewrite /XMSS_SIG_BYTES ifF; first by smt(@W64 pow2_64).
                   rewrite /loadW8 get_setE ifF.
                      + rewrite !to_uintD_small of_uintK 2:/#; 1,2: by smt(@W64 pow2_64). 
                        smt().
                   have ->: Glob.mem{hr}.[to_uint (sm_ptr{hr} + (of_int 4963)%W64) + j] =
                            nth witness (load_buf Glob.mem{hr} (sm_ptr{hr} + (of_int XMSS_SIG_BYTES)%W64) (to_uint i0{hr})) j 
                                 by rewrite  nth_load_buf /#.
                   rewrite H13 nth_load_buf /#. 

seq 3 0 : (
    #pre /\ 
    loadW64 Glob.mem{1} (to_uint smlen_ptr{1}) = mlen{1} + (of_int XMSS_SIG_BYTES)%W64
); last by admit.
    + auto => /> &1 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13.
      do split; last by smt(load_store_W64).
      admit.

seq 1 1 : (
    #pre /\ 
    idx{2} = sk{2}.`Types.idx /\
    0 <= to_uint idx{2} < 1048575 /\
    to_list idx_bytes{1} = sub sk{1} 0 XMSS_INDEX_BYTES
).
    + auto => /> *.
      rewrite /XMSS_INDEX_BYTES.
      apply (eq_from_nth witness); first by rewrite size_to_list size_sub.
      rewrite size_to_list => j?.
      by rewrite get_to_list initiE // nth_sub.

seq 0 3 : (
    #pre /\ 
    address{2} = zero_address /\
    root{2} = sk{2}.`sk_root /\ 
    val root{2} = sub sk{1} (XMSS_INDEX_BYTES + 2*n) n /\
    sk_prf{2} = sk{2}.`Types.sk_prf /\
    val sk_prf{2} = sub sk{1} (XMSS_INDEX_BYTES + n) n 
).
    + auto => /> &1 *.
      rewrite n_val /XMSS_INDEX_BYTES /=; split.
        * apply (eq_from_nth witness); first by rewrite valP n_val size_sub.        
          rewrite valP n_val => j?.
          rewrite nth_sub // /DecodeSkNoOID get_of_list 1:/#.
          rewrite nth_cat !size_cat !valP n_val /= size_EncodeIdx /XMSS_INDEX_BYTES ifT 1:/#.
          rewrite nth_cat !size_cat !valP n_val /= size_EncodeIdx /XMSS_INDEX_BYTES ifF 1:/#.
          by congr; ring.
        * apply (eq_from_nth witness); first by rewrite valP n_val size_sub.        
          rewrite valP n_val => j?.
          rewrite nth_sub // /DecodeSkNoOID get_of_list 1:/#.
          rewrite nth_cat !size_cat !valP n_val /= size_EncodeIdx /XMSS_INDEX_BYTES ifT 1:/#.
          rewrite nth_cat !size_cat !valP n_val /= size_EncodeIdx /XMSS_INDEX_BYTES ifT 1:/#.
          rewrite nth_cat !size_cat !valP n_val /= size_EncodeIdx /XMSS_INDEX_BYTES ifF 1:/#.
          by congr; ring.

seq 1 0 : (#pre /\ to_uint idx{1} = to_uint idx{2}).    
    + ecall {1} (ull_to_bytes_correct idx_bytes{1}).
      auto => /> &1 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9.
      rewrite H8.
      rewrite /W64ofBytes /XMSS_INDEX_BYTES.
      admit.

rcondf {1} 1; first by auto => /> *; rewrite uleE of_uintK /(`<<`) /= /#.
rcondt {1} 1; first by auto => /> *; smt(@W8).

seq 3 1 : (
    #pre /\ 
    t64{1} = idx{1} + W64.one /\
    to_uint t64{1} = to_uint idx_new{2} /\ 
    idx_new{2} = idx{2} + W32.one
).
    + auto => /> &1 ???????????H.
      by rewrite !to_uintD_small 1,2:/# H /=.

wp.
 
seq 2 1 : (
    #{/~sk{1} = DecodeSkNoOID _sk}
     {/~sk{2} = _sk}
     {/~idx{2} = sk{2}.`Types.idx}pre /\
    sk{1} = DecodeSkNoOID sk{2} /\ 
    idx{2} = sk{2}.`Types.idx - W32.one 
).
    + wp; conseq />.
      ecall {1} (ull_to_bytes_3_correct t64{1}).
      auto => /> &1 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 result Hresult.
      do split.
        - rewrite to_uintD_small /#.
        - admit.
        - admit.
        - apply (eq_from_nth witness); first by rewrite valP n_val size_sub.
          rewrite valP n_val => j?.
          rewrite H9 !nth_sub // 1:/#.
          rewrite initiE 1:/# /= initiE 1:/# /=.
          admit.
        - admit.
        - admit.
        - ring.

seq 1 1 : (#pre /\ to_list index_bytes{1} = val idx_bytes{2}).
    + admit.

seq 1 0 : #pre; first by auto.

seq 1 1 : (#pre /\ to_list buf{1} = val _R{2}).
    + admit.
 
seq 17 10 : ( 
  0 <= to_uint _sm_ptr + XMSS_SIG_BYTES <= 18446744073709551615 /\
  sm_ptr{1} = _sm_ptr /\
  sk{1} = DecodeSkNoOID sk{2} /\
  sig{2} = EncodeSignature (to_list signature{1})
); last first.
    + conseq />.
      conseq (: _ ==> to_list signature{1} = load_buf Glob.mem{1} sm_ptr{1} XMSS_SIG_BYTES); first by auto => /> *; congr; assumption.
      while {1} (
         0 <= to_uint sm_ptr{1} + XMSS_SIG_BYTES <= 18446744073709551615 /\
         0 <= i{1} <= 4963 /\
         sub signature{1} 0 i{1} = load_buf Glob.mem{1} sm_ptr{1} i{1}
      )
      (4963 - i{1}); last first.

        * auto => /> &1 *.
          split.
             - apply (eq_from_nth witness); first by rewrite size_sub // size_load_buf //. 
               rewrite size_sub // /#. 
             - move => memL iL.
               split => [/# |].
               move => ?????.
               have ->: iL = XMSS_SIG_BYTES by smt().
               move => <-.
               apply (eq_from_nth witness); first by rewrite size_to_list /XMSS_SIG_BYTES size_sub.
               rewrite size_to_list => j?.
               rewrite get_to_list nth_sub /#.
        * auto => /> &hr H0 H1 H2 H3 H4 *.
          do split; 1,2,4: by smt().
          apply (eq_from_nth witness); first by rewrite size_sub 1:/# size_load_buf /#.
          rewrite size_sub 1:/# => j?.
          rewrite nth_load_buf // nth_sub //=.
          rewrite storeW8E get_setE.
          case (j = i{hr}) => [-> | ?]. 
             - rewrite ifT // to_uintD_small of_uintK /= /#.
             - rewrite ifF; first by rewrite to_uintD_small of_uintK /= /#.
               have ->: signature{hr}.[j] = nth witness (sub signature{hr} 0 i{hr}) j by rewrite nth_sub // /#. 
               rewrite H4 nth_load_buf // /#.

swap {1} 2 -1.
seq  1 0 : (#pre /\ to_list pub_root{1} = val root{2}).
        + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14.
          rewrite H9.
          apply (eq_from_nth witness); first by rewrite size_to_list n_val size_sub. 
          rewrite size_to_list => j?.
          by rewrite get_to_list initiE //= n_val nth_sub.

seq 1 0 : (
        #pre /\
        sub signature{1} XMSS_INDEX_BYTES n = val _R{2}
).
    + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15.
      apply (eq_from_nth witness); first by rewrite valP n_val size_sub.
      rewrite n_val size_sub // => j?.
      rewrite -H14.
      by rewrite nth_sub // initiE 1:/# /= ifT 1:/# /XMSS_INDEX_BYTES /= /copy_8.
 

seq 2 0 : (
    #{/~t64{1} = idx{1} + W64.one}
     {/~to_uint t64{1} = to_uint idx_new{2}}pre /\
     m{2} = load_buf Glob.mem{1} (t64{1} + (W64.of_int 128)) (to_uint mlen{1}) /\
     t64{1} = sm_ptr{1} + (of_int (4963 - 32 - 3 * 32))%W64
).
    + admit. (* Afinal aquilo antes interessa para a prova *)

seq 1 2 : (
  #pre /\
  to_list mhash{1} = val _M'{2}
).
    + exists * Glob.mem{1}, 
               (init (fun (i_0 : int) => signature{1}.[3 + i_0]))%Array32, (* R *)
               pub_root{1}, 
               idx{1},
               t64{1},
               mlen{1}. 
      elim * => Pmem P0 P1 P2 P3 P4.
      wp.
      call {1} (p_hash_message_correct Pmem P0 P1 P2 P3 P4) => [/# |].
      skip => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16.
      do split.
         * admit.
         * admit.
         * smt().
         * admit.
         * move => ???? result ->. 
           congr; congr; last by admit. 
(*   load_buf Pmem (_sm_ptr + (of_int 4963)%W64) (to_uint _mlen) =
load_buf Pmem _m_ptr (to_uint _mlen) *)
           congr.
           apply (eq_from_nth witness); first by rewrite !size_cat !size_to_list !valP n_val size_toByte_64.
           rewrite !size_cat !size_to_list size_toByte_64 // /= => j?.
           congr; congr; last by admit. (*   toByte_64 P2 32 = val idx_bytes{2} *)
           rewrite H14; congr.
           rewrite -H15.
           apply (eq_from_nth witness); first by rewrite n_val size_to_list size_sub.
           rewrite size_to_list => i?.
           rewrite /XMSS_INDEX_BYTES get_to_list initiE //= nth_sub // /#.

swap {2} 3 -2.
seq 2 1 : #pre; first by inline; auto => /> *; smt(zero_addr_setZero).
 
seq 2 1 : (
   #pre /\ 
   to_uint idx_tree{1} = to_uint idx_tree{2} /\
   0 <= to_uint idx_tree{2} < W32.max_uint
).
     + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17.       
       rewrite to_uint_shr of_uintK // h_val d_val /=.
       rewrite H11.
       rewrite to_uint_shr // /#.

seq 2 1 : (#pre /\ ={idx_leaf}).
     + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 *.
       rewrite h_val d_val /= /(`<<`) /= and_comm; congr.
       smt(@W32 pow2_32).

seq 1 1 : (
   #{/~ots_addr{1} = zero_addr}{/~address{2} = zero_address}pre /\ 
   ots_addr{1} = address{2}
).
    + inline; auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 *.
      rewrite /set_tree_addr.
      rewrite tP => j?.
      rewrite !get_setE //.
      case (j = 1) => ?.
         * rewrite ifF 1:/# ifF 1:/#.
           rewrite (: 63 = 2^6 - 1) 1:/# and_mod //=.
           have ->: truncateu8 ((of_int 32))%W256 = (of_int 32)%W8 by rewrite /truncateu8 of_uintK /=. 
           rewrite -H18 /(`>>`) of_uintK /= /truncateu32; congr.
           rewrite to_uint_shr /#.
      case (j = 2) => ?; last by smt(zero_addr_i).
      rewrite /truncateu32; congr.
      rewrite H18 /#.  

