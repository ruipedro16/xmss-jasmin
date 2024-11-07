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

require import Array4 Array8 Array11 Array32 Array64 Array131 Array320 Array352 Array2144 Array2464.

require import Correctness_Address.
require import Correctness_WOTS.
require import Correctness_Mem.
require import Correctness_Conditions.
require import LTReeProof.

require import WArray32.

lemma impl_l p q : p <=> q => (p => q) by smt().
lemma impl_r p q : p <=> q => (q => p) by smt().


lemma treehash_correct ( _sk_seed _pub_seed : W8.t Array32.t, _s _t:W32.t, _addr:W32.t Array8.t): 
    n = XMSS_N /\
    d = XMSS_D /\
    h = XMSS_FULL_HEIGHT /\
    h %/d = XMSS_TREE_HEIGHT /\
    w = XMSS_WOTS_W /\
    len = XMSS_WOTS_LEN /\
    n = XMSS_N /\
    prf_padding_val = XMSS_HASH_PADDING_PRF /\
    prf_kg_padding_val = XMSS_HASH_PADDING_PRF_KEYGEN /\
    padding_len = XMSS_PADDING_LEN /\
    F_padding_val = XMSS_HASH_PADDING_F =>
    equiv [
      M(Syscall).__treehash ~ TreeHash.treehash :

      arg{1}.`2 = _sk_seed /\
      arg{1}.`3 = _pub_seed /\
      arg{1}.`4 = _s /\
      arg{1}.`5 = _t /\
      arg{1}.`6 = _addr /\
      
      arg{2}.`1 = NBytes.insubd (to_list _pub_seed) /\
      arg{2}.`2 = NBytes.insubd (to_list _sk_seed) /\
      arg{2}.`3 = to_uint _s /\
      arg{2}.`4 = to_uint _t /\
      arg{2}.`5 = _addr /\

      0 <= to_uint _t <= h /\
      0 <= to_uint _s <= to_uint _t
      ==>
      to_list res{1} = val res{2}
    ]. 
proof.
rewrite /XMSS_N /XMSS_D /XMSS_TREE_HEIGHT /XMSS_FULL_HEIGHT /XMSS_D /= => [#] n_val d_val h_val tree_height *.
proc => /=.
seq 7 0 : #pre; first by auto.
seq 4 2 : (
  #pre /\
  offset{1} = W64.zero /\
  ots_addr{1} = subtree_addr{1} /\
  ltree_addr{1} = subtree_addr{1} /\
  node_addr{1} = subtree_addr{1} /\
  size stack{2} = h %/ d + 1 /\
  size heights{2} = h %/ d
).
    + auto => /> *; do split;4,5: by smt(size_nseq).
         * rewrite tP => j*.
           rewrite initiE //= get32E pack4E wordP => i?.
           rewrite initiE //= initiE 1:/# /= /init64 initiE 1:/# /= /copy_64 initiE 1:/# /=.
           rewrite  get64E pack8E bits8iE 1:/# initiE 1:/# /= initiE 1:/# //= /init32 initiE 1:/# /= bits8iE /#.
         * rewrite tP => j*.
           rewrite initiE //= get32E pack4E wordP => i?.
           rewrite initiE //= initiE 1:/# /= /init64 initiE 1:/# /= /copy_64 initiE 1:/# /=.
           rewrite  get64E pack8E bits8iE 1:/# initiE 1:/# /= initiE 1:/# //= /init32 initiE 1:/# /= bits8iE /#.
         * rewrite tP => j*.
           rewrite initiE //= get32E pack4E wordP => i?.
           rewrite initiE //= initiE 1:/# /= /init64 initiE 1:/# /= /copy_64 initiE 1:/# /=.
           rewrite  get64E pack8E bits8iE 1:/# initiE 1:/# /= initiE 1:/# //= /init32 initiE 1:/# /= bits8iE /#.
seq 3 0 : (
  #{/~ots_addr{1} = subtree_addr{1}}
   {/~ltree_addr{1} = subtree_addr{1}}
   {/~node_addr{1} = subtree_addr{1}}pre /\
   ots_addr{1} = set_type address{2} 0 /\
   ltree_addr{1} = set_type address{2} 1 /\
   node_addr{1} = set_type address{2} 2
); first by inline {1}; auto.
seq 1 1 : (#pre /\ to_uint offset{1} = offset{2}); first by auto.
swap {1} 1 2.
seq 2 0 : (#pre /\ to_uint upper_bound{1} = 2^t{2}).
    + auto => /> &2 *.
      rewrite (: 31 = 2^5 - 1) 1:/# and_mod // shl_shlw 1:#smt:(@W32) of_uintK to_uint_shl 1:/# /=.
      have ->: to_uint _t %% 32 %% 4294967296 = to_uint _t by smt(modz_small).
      have E: 0 <= 2 ^ h < 4294967296 by rewrite h_val /#.
      smt(@IntDiv @RealExp).

seq 2 2 : (sub _stack{1} 0 n = val (nth witness stack{2} 0)); last first.
    + while {1}
    (#pre /\
     0 <= j{1} <= 32 /\ 
     node{2} = nth witness stack{2} 0 /\
     forall (k : int), 0 <= k < j{1} => root{1}.[k] = nth witness (val (nth witness stack{2} 0)) k) 
    (32 - j{1}); last first.
        * auto => /> &1 &2 ?; split => [/# | j?]; split => [/# |???].
          have ->: j = 32 by smt().
          move => H.
          apply (eq_from_nth witness); first by rewrite valP n_val size_to_list.
          rewrite size_to_list => ??.
          by rewrite get_to_list H.
        * auto => /> &hr H0 ?? H1 *; do split; 1,2,4: by smt().
          move => k??.
          rewrite get_setE 1:/#.
          case (k = j{hr}) => [-> | ?]; last by apply H1 => /#. 
          rewrite -get_to_list -H0.
          by rewrite nth_sub 1:/# get_to_list.

while (
   t{2} = to_uint target_height{1} /\ 
  0 <= t{2} <= h /\ (* Target height *)

  s{2} = to_uint start_index{1} /\ 
  0 <= s{2} <= h /\ (* start index  *) 

  offset{2} = to_uint offset{1} /\  

  (i{2} <> 0 => 0 < offset{2}) /\

  0 <= offset{2} < size stack{2} /\

  size stack{2} = h %/ d + 1 /\ 
  size heights{2} = h %/ d /\

  0 <= i{2} <= 2^t{2} /\
  i{2} <= to_uint target_height{1} /\
  to_uint i{1} = i{2} /\

  to_uint upper_bound{1} = 2^t{2} /\
  
  sk_seed{2} = (insubd (to_list sk_seed{1}))%NBytes /\
  pub_seed{2} = (insubd (to_list pub_seed{1}))%NBytes /\ 
  
    map W32.to_uint (sub heights{1} 0 offset{2}) = sub_list heights{2} 0 offset{2} /\
    sub _stack{1} 0 (n * offset{2}) = sub_list (nbytes_flatten stack{2}) 0 (n * offset{2}) /\
  
    ots_addr{1}.[3] = W32.zero /\ (* type *)
    ltree_addr{1}.[3] = W32.one /\ (* type *)
    node_addr{1}.[3] = W32.of_int 2 /\ (* type *)
  
    ots_addr{1}.[0] = address{2}.[0] /\
    ots_addr{1}.[1] = address{2}.[1] /\
    ots_addr{1}.[2] = address{2}.[2] /\
    ots_addr{1}.[5] = address{2}.[5] /\

    ltree_addr{1}.[0] = address{2}.[0] /\
    ltree_addr{1}.[1] = address{2}.[1] /\
    ltree_addr{1}.[2] = address{2}.[2] /\
    ltree_addr{1}.[5] = address{2}.[5] /\
  
    node_addr{1}.[0] = address{2}.[0] /\
    node_addr{1}.[1] = address{2}.[1] /\
    node_addr{1}.[2] = address{2}.[2] /\
    node_addr{1}.[5] = address{2}.[5] 
); last by admit.


seq 2 0 : (#pre /\ to_uint t32{1} = s{2} + i{2}).
    + auto => /> *; rewrite to_uintD /#.

swap {1} 2 -1.
  
seq 1 2 : (
    #pre /\ sub ots_addr{1} 0 5 = sub address{2} 0 5
).
    + inline {1}; auto => /> &1 &2 ????????????????????????????????H.
      apply (eq_from_nth witness); first by rewrite !size_sub.
      rewrite size_sub // => i?.
      rewrite /set_ots_addr /set_type !nth_sub //.
      rewrite get_setE //=.
      case (i = 4) => [-> |?].
          * by rewrite get_setE //= -H to_uintK.
      rewrite get_setE // ifF 1:/# get_setE //.
      case (i = 3) => [-> // | /#].

seq 1 0 : (#pre /\ ltree_addr{1}.[4] = W32.of_int (s{2} + i{2})).
    + inline {1}; auto => /> &1 &2 ????????????????????????????????H?.
      by rewrite -H to_uintK.

seq 1 4 : (
  #{/~sub ots_addr{1} 0 5 = sub address{2} 0 5}
   {/~ltree_addr{1}.[4] = (of_int (s{2} + i{2}))%W32}pre /\
  val node{2} = to_list buf{1}
); first by admit.
(*
    + inline {1} M(Syscall).__gen_leaf_wots_ M(Syscall)._gen_leaf_wots M(Syscall).__gen_leaf_wots.             
      auto => />.
      exists * pk{1}, ltree_addr2{1}, pub_seed2{1}.
      elim * => P0 P1 P2.
      call (ltree_correct P0 P2 P1) => [/# |].
      wp.
      exists * sk_seed2{1}, pub_seed2{1}, ots_addr2{1}, address{2}.
      elim * => P3 P4 P5 P6.
      call (pkgen_results P3 P4 P5 P6) => [/# |].
      auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34*.
      do split.
*)

seq 2 0 : (#pre /\ to_uint t64{1} = offset{2} * 32).
    + auto => /> &1 &2 *.
      rewrite to_uintM of_uintK /#.  

seq 1 1 : #pre.
    + exists * _stack{1}, buf{1}, t64{1}; elim * => P3 P4 P5.
      call {1} (memcpy_u8u8_3_352_32_post P3 P4 P5).
      auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34.
      do split; 1,2: by smt().
      move => H35 H36 result Ha Hb Hc. 
      do split; 1,2: by smt(size_put).
      apply (eq_from_nth witness); first by rewrite size_sub 1:/# size_sub_list /#.
      rewrite size_sub 1:/# => i?.
      rewrite nth_sub 1:/# /sub_list nth_mkseq //= /nbytes_flatten (nth_flatten witness n).
          - pose P := (fun (s0 : W8.t list) => size s0 = n).
            pose L := (map NBytes.val  (put stack{2} (to_uint offset{1}) node{2})).
            rewrite -(all_nthP P L witness) /P /L size_map size_put H7 d_val h_val /= => j?.
            rewrite (nth_map witness); [rewrite size_put /# |].
            by rewrite valP.
      rewrite (nth_map witness). 
          - rewrite size_put /#.
      rewrite nth_put 1:/# ifF 1:/#.
      have ->:  nth witness (val (nth witness stack{2} (i %/ n))) (i %% n) = nth witness (sub_list (nbytes_flatten stack{2}) 0 (n * to_uint offset{1})) i.
          - rewrite /sub_list nth_mkseq //= /nbytes_flatten (nth_flatten witness n).
               * pose P := (fun (s0 : W8.t list) => size s0 = n).
                 pose L := (map NBytes.val stack{2}).
                 rewrite -(all_nthP P L witness) /P /L size_map H7 d_val h_val /= => j?.
                 by rewrite (nth_map witness) 1:/# valP.
            by rewrite (nth_map witness) 1:/#.
      rewrite -H14 nth_sub // /#.
 
 
seq 2 2 : (
    #{/~offset{2} < size stack{2}}
     {/~to_uint t64{1} = offset{2} * 32}pre /\ 
    to_uint offset{1} <= size stack{2} /\
    0 < offset{2}
).
    + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 ; do split.
        * rewrite to_uintD /#.
        * smt().
        * smt().
        * smt(size_put).
        * apply (eq_from_nth witness); first by rewrite size_map size_sub 1:/# size_sub_list /#.
          rewrite size_map size_sub 1:/# => i?.
          rewrite (nth_map witness).
             - rewrite size_sub /#.
          rewrite nth_sub 1:/#.
          rewrite /sub_list nth_mkseq 1:/#/= nth_put.
             - admit. (* This is false: sub offset tem de passar a ser sub offset - 1 *)
          case (i = to_uint offset{1}) => [-> |?].
             - by rewrite get_setE 1:#smt:(@W64 pow2_64) ifT 1:#smt:(@W64 pow2_64) ifT 1:#smt:(@W64 pow2_64).
          rewrite ifF 1:/# get_setE 1:#smt:(@W64 pow2_64) ifF 1:#smt:(@W64 pow2_64). 
          have ->: to_uint heights{1}.[i] = nth witness (map W32.to_uint (sub heights{1} 0 (to_uint offset{1}))) i.
             - rewrite (nth_map witness); first by rewrite size_sub /#.
               rewrite nth_sub /#.
          rewrite H13 /sub_list nth_mkseq /#.          
        * apply (eq_from_nth witness); first by rewrite size_sub 1:/# size_sub_list /#.
          rewrite size_sub 1:/# => i?.
          rewrite nth_sub 1:/# /sub_list nth_mkseq //= /nbytes_flatten (nth_flatten witness n).
             - pose P := (fun (s0 : W8.t list) => size s0 = n).
               pose L := (map NBytes.val stack{2}).
               rewrite -(all_nthP P L witness) /P /L size_map H7 d_val h_val /= => j?.
               by rewrite (nth_map witness) 1:/# valP.
          rewrite (nth_map witness) 1:/#.
          have ->: _stack{1}.[i] = nth witness (sub _stack{1} 0 (n * to_uint offset{1})) i.
             - rewrite nth_sub //.
                  + admit. (* This is false *)
          rewrite H14 /sub_list nth_mkseq /=. 
             - admit. (* This is false *)
          rewrite /nbytes_flatten (nth_flatten witness n).
             - pose P := (fun (s0 : W8.t list) => size s0 = n).
               pose L := (map NBytes.val stack{2}).
               rewrite -(all_nthP P L witness) /P /L size_map H7 d_val h_val /= => j?.
               by rewrite (nth_map witness) 1:/# valP.
          by rewrite (nth_map witness) 1:/#.   
        * smt(@W64 pow2_64).
        * smt().
 
seq 1 0 : (
    #pre /\ 
    (cond{1} = W8.one <=> treehash_cond heights{1} offset{1})
).
    + ecall {1} (treehash_cond_correct2 heights{1} offset{1}).
      auto => /> /#.  

wp.

while (
  #pre
); first by admit.

auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 *.
rewrite /treehash_cond in H35.
do split.
    - rewrite /treehash_cond in H35.
      admit.
    - rewrite /treehash_cond in H35.
      admit.
    - move => stackL bufL condL heightsL nodeaddrL offsetL addrR heightsR stackR condR *.
      do split.
         + admit.
         + smt().
         + smt().
         + admit.
         + admit.
         + rewrite ultE. admit.
         + rewrite ultE. admit.

qed.

