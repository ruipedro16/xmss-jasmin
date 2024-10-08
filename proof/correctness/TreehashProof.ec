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

require import Array8 Array11 Array32 Array320 Array352.

require import Correctness_Address.


(* stack u8[(XMSS_TREE_HEIGHT + 1) * XMSS_N] _stack; 
   idx = 0;
    while (idx < (1 << XMSS_TREE_HEIGHT))
*)

(* _stack{1} = W8.t Array352.t *)
(* For this proof, the address will be the zero address *)



(* arg{1}

root:W8.t Array32.t
sk_seed:W8.t Array32.t,
pub_seed:W8.t Array32.t, 
s:W32.t, 
target_height:W32.t,
subtree_addr:W32.t Array8.t

*)

(* This only works for kg because of  arg{2}.`3 = 0 /\ arg{2}.`4 = h *)
lemma treehash_correct ( _sk_seed _pub_seed : W8.t Array32.t, _s _t:W32.t, _addr:W32.t Array8.t): 
    n = XMSS_N /\
    d = XMSS_D /\
    h = XMSS_FULL_HEIGHT =>
    equiv [
      M(Syscall).__treehash ~ TreeHash.treehash :
      arg{1}.`2 = _sk_seed /\
      arg{1}.`3 = _pub_seed /\
      arg{1}.`4 = _s /\
      arg{1}.`5 = _t /\
      arg{1}.`6 = _addr /\
      arg{2}.`1 = NBytes.insubd (to_list _pub_seed) /\
      arg{2}.`2 = NBytes.insubd (to_list _sk_seed) /\
      arg{2}.`3 = 0 /\
      arg{2}.`4 = h /\
      arg{2}.`5 = _addr /\

      0 <= to_uint _t <= XMSS_TREE_HEIGHT
      ==>
      to_list res{1} = val res{2}
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

seq 11 3 : (sub _stack{1} 0 32 = val node{2}); last first.
  + while {1} 
    (#pre /\ 0 <= j{1} <= 32 /\
     forall (k : int), 0 <= k < j{1} => root{1}.[k] = _stack{1}.[k])
    (32 - j{1}); last first.
       * auto => /> &1 &2 <-.
         split => [/# | jL rootL].
         split => [/# | ???].
         have ->: jL = 32 by smt().
         move => H1.
         apply (eq_from_nth witness); first by rewrite size_sub // size_to_list.
         rewrite size_to_list => i?.
         rewrite get_to_list nth_sub // /#.
       * auto => /> &hr *.
         do split; 1,2,4: by smt().
         move => k??.
         rewrite get_setE /#. 

seq 7 0 : (true). (* set appropriate condition *)
      + inline {1}.
        auto => />.

swap {1} 1 2.
seq 2 0 : (#pre /\ to_uint upper_bound{1} = 2 ^ t{2}).
      + auto => /> &1 &2.
        rewrite (: 31 = 2^5 - 1) 1:/# and_mod //.
        have ->: truncateu8 ((of_int (to_uint target_height{1} %% 2 ^ 5)))%W32 = 
                 W8.of_int t{2} by admit.
        search (`<<`).
        rewrite shl_shlw.
          * admit.
        admit.


seq 2 2: (sub _stack{1} 0 32 = val (nth witness stack{2} (offset{2} - 1))); last by auto.

while (
          i{2} = to_uint i{1} /\
          to_uint upper_bound{1} = t{2}
); last first.
    + auto => /> &1 &2 *.
      admit.

seq 2 0 : (#pre /\ t32{1} = s{1} + i{1}); first by auto.

inline {1} M(Syscall).__gen_leaf_wots_ M(Syscall)._gen_leaf_wots M(Syscall).__gen_leaf_wots. (* Same as pkgen + ltree *)

admit.
qed.

(*

arg{2}:
pub_seed sk_seed : seed, idx : W32.t, address : adrs

 *)
lemma build_auth_path_correct (_pub_seed _sk_seed : W8.t Array32.t, _idx : W32.t, a : adrs) :
    len = XMSS_WOTS_LEN /\ 
    n = XMSS_N /\
    d = XMSS_D /\
    h = XMSS_FULL_HEIGHT =>
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


      0 <= to_uint _idx < 2^XMSS_FULL_HEIGHT (* ou tree height *)
      ==>
      res{2} = EncodeAuthPath (to_list res{1})
    ].
proof.
rewrite /XMSS_WOTS_LEN /XMSS_N /XMSS_D /XMSS_FULL_HEIGHT => [#] len_val n_val d_val h_val.
proc => /=.
seq 2 3 : (#pre /\ ={j} /\ j{1} = 0 /\ size authentication_path{2} = h). 
  + auto => />; by rewrite size_nseq h_val.

(* With this conseq, proving the last subgoal of the while loop becomes much easier *)
conseq (: _ ==> 
  to_list auth_path{1} = nbytes_flatten authentication_path{2} /\
  size authentication_path{2} = h
).
  + auto => /> &1 &2 H0 H1 l r -> H.
    (* A seta refere se a hipotese to_list `auth_path_L = nbytes_flatten `authentication_path_R *)
    apply auth_path_eq.
    rewrite /EncodeAuthPath /nbytes_flatten !insubdK.
        * by rewrite /P.
        * rewrite /P size_map size_chunk 1:/# size_nbytes_flatten /#.
    apply (eq_from_nth witness).
        * rewrite size_map size_chunk 1:/# size_nbytes_flatten /#.
    rewrite H h_val => i?.
    rewrite (nth_map witness). 
        * rewrite size_chunk 1:/# size_nbytes_flatten /#.
    rewrite /chunk nth_mkseq.
        * rewrite size_nbytes_flatten /#.
    apply nbytes_eq; apply (eq_from_nth witness); first by rewrite !valP.
    rewrite valP n_val => j?.
    rewrite insubdK => />.
        * rewrite /P size_take 1:/# size_drop 1:/# size_nbytes_flatten /#.
    rewrite nth_take 1,2:/# nth_drop 1,2:/# (nth_flatten witness n).
        * pose P := (fun (s : W8.t list) => size s = n).
          pose L := (map NBytes.val r).
          rewrite -(all_nthP P L witness) /P /L size_map H h_val => k?.
          by rewrite (nth_map witness) 1:/# valP.
    rewrite (nth_map witness) /#.
 
while ( 
  0 <= to_uint idx{2} < 1024 /\

  0 <= j{1} <= h /\ ={j} /\
  size authentication_path{2} = h /\

  idx{2} = i{1} /\
  to_list sk_seed{1}  = val sk_seed{2} /\
  to_list pub_seed{1} = val pub_seed{2} /\

  forall (k : int), 0 <= k < n * j{1} => auth_path{1}.[k] = nth witness (nbytes_flatten authentication_path{2}) k
); last first.
    + auto => /> &2 *. 
      do split; 1,4,5: by smt().
        * by rewrite insubdK // /P size_to_list n_val.
        * by rewrite insubdK // /P size_to_list n_val.
        * move => authPathL authPathR j H0 H1 H2 H3 H4 ?? H5.
          have j_val: j = h by smt().
          clear H0 H1 H2 H3.
          rewrite /EncodeAuthPath. 
          apply (eq_from_nth witness); first by rewrite size_to_list size_nbytes_flatten_2 H4 n_val h_val.
          rewrite size_to_list => i?.
          by rewrite get_to_list H5 // n_val j_val h_val.
seq 3 1 : (#pre /\ to_uint k{1} = k{2}); first by auto.
seq 3 0 : (#pre /\ to_uint s{1} = k{2} * 2^j{1}).
    + auto => /> &1 &2 *. 
      rewrite shl_shlw 1:/# to_uint_shl 1:/#. 
      admit.

seq 1 1 : (#pre /\ to_list node{1} = val t{2}).
    + inline {1} M(Syscall).__treehash_ M(Syscall)._treehash.
      wp.
      exists * sk_seed1{1}, pub_seed1{1}, s1{1}, t0{1}, subtree_addr0{1}.
      elim * => P0 P1 P2 P3 P4.
      call {1} (treehash_correct P0 P1 P2 P3 P4) => [/# |].
      auto => /> &1 &2 *. admit.

auto => /> &1 &2 ????H??H0???H1. 
do split; 1,2,5,6: by smt().
    * by rewrite size_put.
move => k??.
rewrite initiE 1:/# => />.
rewrite /nbytes_flatten (nth_flatten witness n).
   * pose P := (fun (s : W8.t list) => size s = n).
     pose L := (map NBytes.val (put authentication_path{2} j{2} t{2})).
     rewrite -(all_nthP P L witness) /P /L size_map size_put H h_val => j?.
     by rewrite (nth_map witness) 1:#smt:(size_put) valP.
rewrite (nth_map witness) 1:#smt:(size_put) nth_put 1:/#.
case (j{2} * 32 <= k && k < j{2} * 32 + 32) => H2.
   * rewrite ifT 1:/# -H1 get_to_list /#.
   * rewrite ifF 1:/# H0 1:/# /nbytes_flatten (nth_flatten witness n).
       - pose P := (fun (s0 : W8.t list) => size s0 = n).
         pose L := (map NBytes.val authentication_path{2}).
         rewrite -(all_nthP P L witness) /P /L size_map H h_val => j?.
         by rewrite (nth_map witness) 1:/# valP.
     by rewrite (nth_map witness) 1:/#.
qed.
 
