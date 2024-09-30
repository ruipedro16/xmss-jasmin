pragma Goals : printall.

require import AllCore List RealExp IntDiv Distr DList.
from Jasmin require import JModel JArray.

require import BitEncoding.
(*---*) import BitChunking.

require import StdBigop. 
(*---*) import Bigint.

require import Params XMSS_MT_Params Types Address BaseW WOTS LTree XMSS_MT_TreeHash XMSS_MT_PRF.
require import XMSS_IMPL Parameters.
require import Repr2 Utils2.

require import Termination.

require import Array8 Array11 Array32 Array320 Array352.

require import Correctness_Address.


(* stack u8[(XMSS_TREE_HEIGHT + 1) * XMSS_N] _stack; 
   idx = 0;
    while (idx < (1 << XMSS_TREE_HEIGHT))
*)

(* _stack{1} = W8.t Array352.t *)
(* For this proof, the address will be the zero address *)
lemma treehash_correct (_auth_path : W8.t Array320.t, _sk_seed _pub_seed : W8.t Array32.t,
                        _idx:W32.t, _addr:W32.t Array8.t) : 
    n = XMSS_N /\
    d = XMSS_D /\
    h = XMSS_FULL_HEIGHT =>
    equiv [
      M(Syscall).__treehash ~ TreeHash.treehash :
      arg{1}.`2 = _auth_path /\
      arg{1}.`3 = _sk_seed /\
      arg{1}.`4 = _pub_seed /\
      arg{1}.`5 = _idx /\
      arg{1}.`6 = _addr /\
      arg{2}.`1 = NBytes.insubd (to_list _pub_seed) /\
      arg{2}.`2 = NBytes.insubd (to_list _sk_seed) /\
      arg{2}.`3 = 0 /\
      arg{2}.`4 = h /\
      arg{2}.`5 = _addr
      ==>
      to_list res{1}.`1 = val res{2}
    ].
proof.
rewrite /XMSS_N /XMSS_D /XMSS_FULL_HEIGHT => [#] n_val d_val h_val.
proc => /=.
seq 7 0 : #pre; first by auto.
seq 0 1 : (#pre /\ size stack{2} = h + 1); first by auto => />; rewrite size_nseq #smt:(ge0_h ge0_d). 
seq 1 1 : (#pre /\ to_uint offset{1} = offset{2}); first by auto. 
seq 1 0 : (#pre /\ ots_addr{1}= zero_addr).
  + inline {1} 1; wp.
    ecall {1} (zero_addr_res ots_addr{1}).
    auto.
seq 1 0 : (#pre /\ ltree_addr{1}= zero_addr).
  + inline {1} 1; wp.
    ecall {1} (zero_addr_res ots_addr{1}).
    auto.
seq 1 0 : (#pre /\ node_addr{1}= zero_addr).
  + inline {1} 1; wp.
    ecall {1} (zero_addr_res ots_addr{1}).
    auto.
seq 8 3 : (sub _stack{1} 0 32 = val node{2}); last first.
  + while {1} 
    (
     0 <= j{1} <= 32 /\
     (forall (k : int), 0 <= k < j{1} => root{1}.[k] = _stack{1}.[k])
    ) 
    (32 - j{1}).
       - auto => /> *. 
         do split; 1,2,4: by smt().  
         move => k??.
         rewrite get_setE // /#.
       - auto => /> &1 &2 H0. 
         split => [/# | jL rootL *].
         split => [/# | ???].
         have ->: jL = 32 by smt(). 
         move => ?.
         apply (eq_from_nth witness); [by rewrite valP n_val size_to_list |].
         rewrite size_to_list => j?.
         rewrite get_to_list -H0 nth_sub // /#.
seq 6 0 : (
      auth_path{1} = _auth_path /\
      sk_seed{1} = _sk_seed /\
      pub_seed{1} = _pub_seed /\
      leaf_idx{1} = _idx /\
      subtree_addr{1} = _addr /\
      pub_seed{2} = (insubd (to_list _pub_seed))%NBytes /\
      sk_seed{2} = (insubd (to_list _sk_seed))%NBytes /\ 
      address{2} = _addr /\
      size stack{2} = h + 1 /\
      to_uint offset{1} = offset{2} /\
      s{2} = 0 /\ t{2} = 10 /\

      ots_addr{1}.[0] = _addr.[0] /\
      ots_addr{1}.[1] = _addr.[1] /\ 
      ots_addr{1}.[2] = _addr.[2] /\ 
      ots_addr{1}.[3] = W32.zero /\
      ots_addr{1}.[4] = W32.zero /\
      ots_addr{1}.[5] = W32.zero /\
      ots_addr{1}.[6] = W32.zero /\
      ots_addr{1}.[7] = W32.zero /\

      ltree_addr{1}.[0] = _addr.[0] /\
      ltree_addr{1}.[1] = _addr.[1] /\ 
      ltree_addr{1}.[2] = _addr.[2] /\ 
      ltree_addr{1}.[3] = W32.one /\
      ltree_addr{1}.[4] = W32.zero /\
      ltree_addr{1}.[5] = W32.zero /\
      ltree_addr{1}.[6] = W32.zero /\
      ltree_addr{1}.[7] = W32.zero /\

      node_addr{1}.[0] = _addr.[0] /\
      node_addr{1}.[1] = _addr.[1] /\ 
      node_addr{1}.[2] = _addr.[2] /\ 
      node_addr{1}.[3] = W32.of_int 2 /\
      node_addr{1}.[4] = W32.zero /\
      node_addr{1}.[5] = W32.zero /\
      node_addr{1}.[6] = W32.zero /\
      node_addr{1}.[7] = W32.zero
); first by inline {1}; auto.
seq 3 2 : (sub _stack{1} 0 32 = val (nth witness stack{2} (offset{2} - 1))); last by auto.
inline M(Syscall).__gen_leaf_wots_ M(Syscall)._gen_leaf_wots M(Syscall).__gen_leaf_wots.
while (
  to_uint idx{1} = i{2} /\
  0 <= i{2} <= 2 ^ 10 /\
  pk{1} = DecodeWotsPk pk{2} /\
  to_list leaf{1} = val node{2} 
  (* Add stuff about _stack *)
); last first.
    + admit.
(*
    RHS 
    1) set_type 0      => changes a.[3]
    2) set_ots 1       => changes a.[4]

    4) Set type 1      => changes a.[3]
    5) set_tree 1      => changes a.[1,2]

    7) set_type 2           => changes a.[3]
    8) set_tree_height 0    => changes a.[5]
    9) set_tree_index i+1   => changes a.[6]
*)
swap {1} 2 -1.
seq 2 2 : (#pre /\ ots_addr{1} = address{2}).
    + inline; auto. admit.

qed.
