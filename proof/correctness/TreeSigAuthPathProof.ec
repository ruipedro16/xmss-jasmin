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

require import WArray32.


lemma build_auth_path_correct (_pub_seed _sk_seed : W8.t Array32.t, _idx : W32.t, a : adrs) :
    len = XMSS_WOTS_LEN /\ 
    n = XMSS_N /\
    d = XMSS_D /\
    h = XMSS_TREE_HEIGHT =>
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

      0 <= to_uint _idx < 2 ^ XMSS_FULL_HEIGHT - 1
      ==>
      res{2} = EncodeAuthPath (to_list res{1})
    ].
proof.
rewrite /XMSS_WOTS_LEN /XMSS_N /XMSS_D /XMSS_TREE_HEIGHT => [#] len_val n_val d_val h_val.
proc => /=.
seq 2 3 : (#pre /\ ={j} /\ j{1} = 0 /\ size authentication_path{2} = h). 
  + auto => />; by rewrite size_nseq h_val.

(* With this conseq, proving the last subgoal of the while loop becomes much easier *)
conseq (: _ ==> 
  to_list auth_path{1} = nbytes_flatten authentication_path{2} /\
  size authentication_path{2} = h
).
    + admit.

(* Rewrite #pre *)
conseq ( :
  to_list sk_seed{1} = val sk_seed{2} /\
  to_list pub_seed{1} = val pub_seed{2} /\
  addr{1} = address{2} /\
  ={j} /\ j{1} = 0 /\
  i{1} = idx{2} /\ 
  0 <= to_uint idx{2} < 2 ^ XMSS_FULL_HEIGHT - 1 /\
  size authentication_path{2} = 10
  ==> _
).
    + auto => /> *; split.
        * apply (eq_from_nth witness); first by rewrite valP size_to_list n_val.
          rewrite size_to_list => j?.
          by rewrite insubdK // /P size_to_list n_val.
        * split => [| /#].
          apply (eq_from_nth witness); first by rewrite valP size_to_list n_val.
          rewrite size_to_list => j?.
          by rewrite insubdK // /P size_to_list n_val.

 while (
  to_list sk_seed{1} = val sk_seed{2} /\
  to_list pub_seed{1} = val pub_seed{2} /\
  addr{1} = address{2} /\
  i{1} = idx{2} /\
  ={j} /\ 0 <= j{2} <= 10 /\ 
  size authentication_path{2} = 10 /\

  (0 <= to_uint idx{2} < 2 ^ XMSS_FULL_HEIGHT - 1) /\

  forall (k : int), 0 <= k < n * j{1} => auth_path{1}.[k] = nth witness (nbytes_flatten authentication_path{2}) k
); last first.
    + auto => /> &1 &2 ?????.
      split => [/# | authL authR j ????H0].
      have ->: j = h by smt().
      rewrite n_val h_val /= => H1.
      split => [| /#].
      apply (eq_from_nth witness); first by rewrite size_to_list size_nbytes_flatten_2 H0 n_val.
      rewrite size_to_list => ??.
      by rewrite  get_to_list H1.

seq 4 1 : (
    #pre /\ 
    to_uint k{1} = k{2} * 2^j{1} /\
    k{2} = to_uint ((idx{2} `>>` (of_int j{2})%W8) `^` W32.one)
).
    + auto => /> &1 &2 ? H *.
      rewrite /XMSS_FULL_HEIGHT /= in H.
      rewrite shl_shlw 1:/# /(`>>`) of_uintK to_uint_shl //. 
