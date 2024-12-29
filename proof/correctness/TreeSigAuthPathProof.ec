pragma Goals : printall.

require import AllCore List RealExp IntDiv Distr DList.
from Jasmin require import JModel JArray.

require import BitEncoding.
(*---*) import BitChunking.

require import StdBigop. 
(*---*) import Bigint.

require import Params XMSS_MT_Params Types XMSS_MT_Types Address Hash BaseW WOTS LTree XMSS_MT_TreeHash XMSS_MT_PRF.
require import XMSS_IMPL Parameters.
require import Repr2 Utils2.

import AuthPath.

require import Array4 Array8 Array11 Array32 Array131 Array320 Array352 Array2144 Array2464.

require import Correctness_Address.
require import Correctness_WOTS.
require import Correctness_Mem.
require import Correctness_TreehashCondition.
require import FinalTreeHashProof.

require import WArray32.

lemma build_auth_path_correct (_pub_seed _sk_seed : W8.t Array32.t, _idx : W32.t, a : adrs) :
    n = XMSS_N /\
    d = XMSS_D /\
    h = XMSS_FULL_HEIGHT /\
    h %/ d = XMSS_TREE_HEIGHT /\
    w = XMSS_WOTS_W /\
    len = XMSS_WOTS_LEN /\
    prf_padding_val = XMSS_HASH_PADDING_PRF /\
    prf_kg_padding_val = XMSS_HASH_PADDING_PRF_KEYGEN /\
    padding_len = XMSS_PADDING_LEN /\ F_padding_val = XMSS_HASH_PADDING_F =>
    equiv[
      M(Syscall).__build_auth_path ~ TreeSig.buildAuthPath :
      arg{1}.`2 = _sk_seed /\
      arg{1}.`3 = _pub_seed /\
      arg{1}.`4 = _idx /\
      arg{1}.`5 = a /\

      arg{2}.`1 = NBytes.insubd (to_list _pub_seed) /\
      arg{2}.`2 = NBytes.insubd (to_list _sk_seed) /\
      arg{2}.`3 = _idx /\
      arg{2}.`4 = a /\

      a.[4] = W32.zero /\

      0 <= to_uint _idx < 2 ^ XMSS_FULL_HEIGHT - 1
      ==>
      res{2} = EncodeAuthPath (to_list res{1})
    ].
proof.
rewrite /XMSS_WOTS_LEN /XMSS_N /XMSS_D /XMSS_FULL_HEIGHT => [#] n_val d_val h_val *.
proc => /=.

seq 2 3 : (
  #pre /\ 
  ={j} /\ j{1} = 0 /\ 
  size authentication_path{2} = h %/ d
). 
  + auto => />; by rewrite size_nseq h_val /#.

(* With this conseq, proving the last subgoal of the while loop becomes much easier *)
conseq (: _ ==> 
  to_list auth_path{1} = nbytes_flatten authentication_path{2} /\
  size authentication_path{2} = h %/ d
).
    + auto => /> &1 &2 H0 H1 H2 authPathL authPathR -> H3.
      apply auth_path_eq.
      rewrite insubdK //.
      rewrite /EncodeAuthPath insubdK.
         * rewrite /P size_map n_val size_chunk // size_nbytes_flatten H3 n_val /#.
      apply (eq_from_nth witness).
         * rewrite n_val size_map size_chunk // size_nbytes_flatten H3 /#.
      rewrite H3 d_val h_val /= => j?.
      rewrite (nth_map witness).
         * rewrite n_val size_chunk // size_nbytes_flatten H3 /#.      
      rewrite /chunk nth_mkseq /=.
         * rewrite size_nbytes_flatten /#.        
      apply nbytes_eq.
      rewrite insubdK.
         * rewrite n_val /P size_take // size_drop 1:/# size_nbytes_flatten /#.
      apply (eq_from_nth witness).
         * rewrite valP n_val size_take // size_drop 1:/# size_nbytes_flatten /#. 
      rewrite valP n_val => i?.
      rewrite nth_take // 1:/# nth_drop 1,2:/# nth_nbytes_flatten /#.

(* Rewrite #pre *)
conseq ( :
  to_list sk_seed{1} = val sk_seed{2} /\
  to_list pub_seed{1} = val pub_seed{2} /\
  addr{1} = address{2} /\
  ={j} /\ j{1} = 0 /\
  i{1} = idx{2} /\ 
  0 <= to_uint idx{2} < 2 ^ XMSS_FULL_HEIGHT - 1 /\
  size authentication_path{2} = h %/ d /\ 
  addr{1}.[4] = W32.zero
  ==> _
).
    + auto => /> *; split.
        * apply (eq_from_nth witness); first by rewrite valP size_to_list n_val.
          rewrite size_to_list => j?.
          by rewrite insubdK // /P size_to_list n_val.
        * apply (eq_from_nth witness); first by rewrite valP size_to_list n_val.
          rewrite size_to_list => j?.
          by rewrite insubdK // /P size_to_list n_val.

while (
  to_list sk_seed{1} = val sk_seed{2} /\
  to_list pub_seed{1} = val pub_seed{2} /\
  addr{1} = address{2} /\
  i{1} = idx{2} /\
  ={j} /\ 0 <= j{2} <= h %/ d /\ 
  size authentication_path{2} = h %/ d /\
  
  addr{1}.[4] = W32.zero /\

  (0 <= to_uint idx{2} < 2 ^ XMSS_FULL_HEIGHT - 1) /\

  forall (k : int), 0 <= k < n * j{1} => auth_path{1}.[k] = nth witness (nbytes_flatten authentication_path{2}) k
); last first.
    + auto => /> &1 &2 *.
      split => [/# | authL authR j ????H0].

      have ->: j = h %/ d by smt().
      rewrite n_val h_val /= => H1.
      apply (eq_from_nth witness).
         * rewrite size_to_list size_nbytes_flatten n_val H0 /#.
      rewrite size_to_list => ??.
      rewrite get_to_list H1 /#.        

seq 4 1 : (
    #pre /\ 
    to_uint k{1} = k{2} * 2^j{1} /\
    k{2} = to_uint ((idx{2} `>>` (of_int j{2})%W8) `^` W32.one)
).
    + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.
      rewrite shl_shlw 1:/# /(`>>`) of_uintK to_uint_shl //. 
      rewrite (: j{2} %% W8.modulus %% 32 = j{2}) 1:/#.
      apply modz_small.
      split; admit.
 
seq 1 1 : (#pre /\ to_list node{1} = val t{2}).
    + inline {1} 1.
      inline {1} 13.
      wp; sp.
      exists * pub_seed{1}, sk_seed{1}, k{1}, (of_int j{1})%W32, addr{1}.
      elim * => P0 P1 P2 P3 P4.
      call {1} (treehash_correct P1 P0 P2 P3 P4) => [/# |].
      skip => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 ->. 
      do split; 1,2:smt(@NBytes).
         * rewrite of_uintK /#.
         * rewrite of_uintK /#.
         * smt(@W32 pow2_32).
         * admit.
         * admit.

auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 *.
do split; 1,2,5,6: by smt().
    - rewrite size_put /#.
    - move => k??.
      rewrite nth_nbytes_flatten.
         * rewrite size_put /#.
      rewrite initiE 1:/# /=.
      rewrite nth_put 1:/#.
case (j{2} * 32 <= k && k < j{2} * 32 + 32) => ?.
    + rewrite ifT 1:/# -H12 get_to_list /#.
    + rewrite ifF 1:/# H8 1:/# nth_nbytes_flatten // /#.
qed.

lemma treesig_correct (_m : W8.t Array32.t, _sk : xmss_sk, _idx_sig : W32.t, _addr : W32.t Array8.t) :
    n = XMSS_N /\
    d = XMSS_D /\
    h = XMSS_FULL_HEIGHT /\
    h %/ d = XMSS_TREE_HEIGHT /\
    w = XMSS_WOTS_W /\
    len = XMSS_WOTS_LEN /\
    prf_padding_val = XMSS_HASH_PADDING_PRF /\
    prf_kg_padding_val = XMSS_HASH_PADDING_PRF_KEYGEN /\
    padding_len = XMSS_PADDING_LEN /\ 
    F_padding_val = XMSS_HASH_PADDING_F /\
    floor (log2 w%r) = XMSS_WOTS_LOG_W /\ 
    len1 = XMSS_WOTS_LEN1 /\
    len2 = XMSS_WOTS_LEN2 => 
    equiv [
      M(Syscall).__tree_sig ~ TreeSig.treesig:
      arg{1}.`2 = _m /\
      arg{1}.`3 = DecodeSkNoOID _sk /\
      arg{1}.`4 = _idx_sig /\
      arg{1}.`5 = _addr /\
      
      arg{2}.`1 = NBytes.insubd (to_list _m) /\
      arg{2}.`2 = _sk /\
      arg{2}.`3 = _idx_sig /\
      arg{2}.`4 = _addr /\

      _addr.[4] = W32.zero /\

      (* Isto e a negacao da condicao idx >= ((1ULL << params->full_height) - 1) usada p verificar se ainda se pode assinat com uma determinada chave *)
      (* FIXME: e 2^XMSS_FULL_HEIGHT - 1 e nao 2^XMSS_FULL_HEIGHT *)
      0 <= to_uint _idx_sig < 2 ^ XMSS_FULL_HEIGHT - 1

      ==>
      res{2} = EncodeReducedSignature (to_list res{1}.`1)
    ].
proof.
rewrite /XMSS_WOTS_LEN /XMSS_N /XMSS_D /XMSS_FULL_HEIGHT => [#] n_val d_val h_val *.

proc => /=.
seq 6 0 : (
  #pre /\
  to_list pub_seed{1} = sub sk{1} (XMSS_INDEX_BYTES + 3*32) 32 /\
  to_list sk_seed{1} = sub sk{1} XMSS_INDEX_BYTES 32
).
    + auto => /> *; split.
         * apply (eq_from_nth witness); first by rewrite size_to_list size_sub.
           rewrite size_to_list => i?.
           rewrite get_to_list initiE // nth_sub //.
         * apply (eq_from_nth witness); first by rewrite size_to_list size_sub.
           rewrite size_to_list => i?.
           by rewrite get_to_list initiE // nth_sub.

seq 0 2 : (
  #pre /\
  val sk_seed{2} = to_list sk_seed{1} /\
  val pub_seed{2} = to_list pub_seed{1}
).
    + auto => /> &1 ??? -> ->; split; rewrite /DecodeSkNoOID.
       * apply (eq_from_nth witness); first by rewrite valP size_sub.
         rewrite valP n_val => i?.
         rewrite nth_sub // get_of_list 1:/#.
         rewrite nth_cat ifT.
             - rewrite !size_cat valP n_val size_take //.
               rewrite ifT; [by rewrite size_W32toBytes |].
               rewrite !valP /#.
         rewrite nth_cat ifT.
             - rewrite !size_cat valP n_val size_take //.
               rewrite ifT; [by rewrite size_W32toBytes |].
               rewrite !valP /#.
         rewrite nth_cat ifT.
             - rewrite !size_cat valP n_val size_take //.
               rewrite ifT; [by rewrite size_W32toBytes | smt()].
         rewrite nth_cat ifF; [by rewrite size_take // size_W32toBytes /# |].
         rewrite size_take // size_W32toBytes /#.
       * apply (eq_from_nth witness); first by rewrite valP n_val size_sub.
         rewrite valP n_val => i?.
         rewrite nth_sub // get_of_list 1:/# nth_cat ifF.
             - rewrite !size_cat !valP n_val size_take // size_W32toBytes /#.
         rewrite !size_cat !valP n_val size_take // size_W32toBytes /#.

(* Rewrite #pre *)
conseq (:
  M{2} = (insubd (to_list m{1}))%NBytes /\
  idx{2} = idx_sig{1} /\
  address{2} = addr{1} /\
  val sk_seed{2} = to_list sk_seed{1} /\
  val pub_seed{2} = to_list pub_seed{1} /\
  addr{1}.[4] = W32.zero /\
  0 <= to_uint idx_sig{1} < 2 ^ XMSS_FULL_HEIGHT - 1
  ==>
  _
); first by auto.
 
seq 1 1 : (#pre /\ auth{2} = EncodeAuthPath (to_list auth_path{1})).
    + exists * pub_seed{1}, sk_seed{1}, idx_sig{1}, addr{1}.
      elim * => P0 P1 P2 P3.
      call (build_auth_path_correct P0 P1 P2 P3) => [/# |].
      skip => /> &2 <- <- ???; by smt(@NBytes).
 
print set_ots_addr.

seq 2 2 : (#{/~addr{1}.[4] = W32.zero}pre).
    + inline {1}; auto => /> &1 &2 *.
      rewrite /set_type /set_ots_addr tP => i?. 
      rewrite !get_setE //.
      admit.

seq 1 1 : (sig_ots{2} = EncodeWotsSignature sig_ots{1} /\ auth{2} = EncodeAuthPath (to_list auth_path{1})).
    + inline {1} M(Syscall).__wots_sign_ M(Syscall)._wots_sign.
      sp; wp.
      exists * msg0{1}, seed0{1}, pub_seed{1}, addr1{1}, Glob.mem{1}.
      elim * => P0 P1 P2 P3 Pmem.
      call {1} (wots_sign_seed_corect Pmem P0 P1 P2 P3) => [/# |].
      skip => /> &1 &2 <- <- *; do split.
           - by rewrite insubdK /P // size_to_list n_val.
           - smt(@NBytes).
           - smt(@NBytes).

seq 2 0 : (#pre /\ sub sig{1} 0 XMSS_WOTS_SIG_BYTES = to_list sig_ots{1}).
    + while {1} 
      (#pre /\ 
       0 <= i{1} <= 2144 /\
       forall (k : int), 0 <= k < i{1} => sig{1}.[k] = sig_ots{1}.[k])
      (2144 - i{1}); last first.
           * auto => /> &1; split => [/# | i sig].
             split => [/# | ???].
             have ->: i = 2144 by smt().
             move => H. 
             apply (eq_from_nth witness); first by rewrite size_to_list size_sub.
             rewrite size_sub // => j?.
             rewrite nth_sub //=. 
             by apply H.
      auto => /> &hr ?? H*; do split; 1,2,4: by smt().
      move => k??.
      rewrite get_setE 1:/#.
      case (k = i{hr}) => [-> // | ?].
      apply H => /#.
 
seq 3 0 : (#pre /\ sub sig{1} XMSS_WOTS_SIG_BYTES 320 = to_list auth_path{1}).
    + while {1} 
      (#pre /\ 
       aux{1} = 320 /\
       0 <= i{1} <= 320 /\
       forall (k : int), 0 <= k < i{1} => sig{1}.[XMSS_WOTS_SIG_BYTES + k] = auth_path{1}.[k])
      (320 - i{1}); last first.
           * auto => /> &1 ?; split => [/# | i sig].
             split => [/# | ????].
             have ->: i = 320 by smt().
             move => H. 
             apply (eq_from_nth witness); first by rewrite size_to_list size_sub.
             rewrite size_sub // => j?.
             rewrite nth_sub //=. 
             by apply H.
      auto => /> &hr H *; do split; 2,3,5: by smt().
           * apply (eq_from_nth witness); first by rewrite size_to_list size_sub.
             rewrite size_sub // /XMSS_WOTS_SIG_BYTES => j?.
             by rewrite nth_sub // -H get_setE 1:/# ifF 1:/# /= nth_sub.
           * move => k??.
             rewrite get_setE 1:/#.
             case (k = i{hr}) => [-> // | ?].
             rewrite ifF /#.

auto => /> &1 H0 H1.
rewrite /EncodeReducedSignature.
rewrite /XMSS_WOTS_SIG_BYTES in H0.
rewrite /XMSS_WOTS_SIG_BYTES in H1.
congr.
        + rewrite encodewotssig_list_array; congr.
          rewrite -H0.
          apply (eq_from_nth witness); first by rewrite size_sub // size_sub_list.
          rewrite size_sub // => j?.
          by rewrite nth_sub // /sub_list nth_mkseq .
        + congr.
          apply (eq_from_nth witness); first by rewrite size_to_list size_sub_list.
          rewrite size_to_list => j?.
          by rewrite -H1 nth_sub // /sub_list nth_mkseq.
qed.
