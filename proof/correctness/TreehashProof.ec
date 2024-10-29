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

require import Array4 Array8 Array11 Array32 Array131 Array320 Array352 Array2144 Array2464.

require import Correctness_Address.
require import Correctness_WOTS.
require import Correctness_Mem.
require import Correctness_Conditions.
(* require import LTReeProof. *)

require import WArray32.

(* 
{1} => proc __treehash (root:W8.t Array32.t, sk_seed:W8.t Array32.t,
                   pub_seed:W8.t Array32.t, start_index:W32.t,
                   target_height:W32.t, subtree_addr:W32.t Array8.t)

{2} => proc treehash(pub_seed sk_seed : seed, s t : int, address : adrs) : nbytes
*)
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
 
swap {2} 3 -2.
seq 8 1: (#pre /\ offset{1} = W64.zero /\ offset{2} = 0); first by auto.

seq 11 4 : (sub _stack{1} 0 n = val (nth witness stack{2} 0)); last first.
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

seq 0 2 : (#pre /\ size stack{2} = (h %/d + 1) /\ size heights{2} = (h %/ d)).
      + auto => /> *; rewrite !size_nseq /#.

seq 1 0 : (#pre /\ ots_addr{1} = subtree_addr{1}).
      + auto => /> *.
        rewrite tP => j?.
        rewrite initiE //= get32E pack4E wordP => i?.
        rewrite initiE //= initiE 1:/# /= /init64 initiE 1:/# /= /copy_64 initiE 1:/# /=.
        rewrite  get64E pack8E bits8iE 1:/# initiE 1:/# /= initiE 1:/# //= /init32 initiE 1:/# /= bits8iE /#.

seq 1 0 : (#pre /\ ltree_addr{1} = subtree_addr{1}).
      + auto => /> ??.
        rewrite tP => j*.
        rewrite initiE //= get32E pack4E wordP => i?.
        rewrite initiE //= initiE 1:/# /= /init64 initiE 1:/# /= /copy_64 initiE 1:/# /=.
        rewrite  get64E pack8E bits8iE 1:/# initiE 1:/# /= initiE 1:/# //= /init32 initiE 1:/# /= bits8iE /#.

seq 1 0 : (#pre /\ node_addr{1} = subtree_addr{1}).
      + auto => /> ??.
        rewrite tP => j*.
        rewrite initiE //= get32E pack4E wordP => i?.
        rewrite initiE //= initiE 1:/# /= /init64 initiE 1:/# /= /copy_64 initiE 1:/# /=.
        rewrite  get64E pack8E bits8iE 1:/# initiE 1:/# /= initiE 1:/# //= /init32 initiE 1:/# /= bits8iE /#.

seq 4 0 : (
      #{/~ ots_addr{1} = subtree_addr{1}}
       {/~ ltree_addr{1} = subtree_addr{1}}
       {/~ node_addr{1} = subtree_addr{1}}pre /\
      ots_addr{1} = set_type subtree_addr{1} 0 /\
      ltree_addr{1} = set_type subtree_addr{1} 1 /\
      node_addr{1} = set_type subtree_addr{1} 2
); first by inline; auto.

swap {1} 1 2.

seq 2 0 : (#pre /\ to_uint upper_bound{1} = 2^t{2}).
    + auto => /> &2. 
      rewrite d_val h_val /= => *.
      rewrite (: 31 = 2^5 - 1) 1:/# and_mod // shl_shlw 1:#smt:(@W32) of_uintK to_uint_shl 1:/# /=.
      have ->: to_uint _t %% 32 %% 4294967296 = to_uint _t by smt(modz_small).
      have E: 0 <= 2 ^ h < 4294967296 by rewrite h_val /#.
      smt(@IntDiv @RealExp).

(* Rewrite #pre *)
conseq (:
  size stack{2} = h %/ d + 1 /\ 
  size heights{2} = h %/ d /\

  pub_seed{2} = (insubd (to_list pub_seed{1}))%NBytes /\
  sk_seed{2} = (insubd (to_list sk_seed{1}))%NBytes /\
  
  address{2} = subtree_addr{1} /\

  ots_addr{1} = set_type address{2} 0 /\
  ltree_addr{1} = set_type address{2} 1 /\
  node_addr{1} = set_type address{2} 2 /\
  subtree_addr{1} = address{2} /\

  ots_addr{1}.[3] = W32.zero /\
  ltree_addr{1}.[3] = W32.one /\
  node_addr{1}.[3] = W32.of_int 2 /\

  offset{2} = to_uint offset{1} /\ 
  offset{1} = W64.zero /\

  t{2} = to_uint target_height{1} /\ 
  0 <= t{2} <= h /\

  s{2} = to_uint start_index{1} /\
  0 <= s{2} <= t{2} /\

  size stack{2} = h %/ d + 1 /\ 
  size heights{2} = h %/ d /\

  to_uint upper_bound{1} = 2^t{2}
  ==> 
  _
); first by auto.

(*

=> The stack contains nodes at varying heights, with the height of each node stored in the heights array at the corresponding offset.

=> When two nodes on the stack are at the same height, they are combined (& removed from the stack), and the resulting node is pushed onto the stack 

=> No fim, offset = 1 (esta um nodo na stack 
*) 
 
while ( 
  t{2} = to_uint target_height{1} /\ 
  0 <= t{2} <= h /\ (* Target height *)

  s{2} = to_uint start_index{1} /\ 
  0 <= s{2} <= h /\ (* start index  *) 

  offset{2} = to_uint offset{1} /\  

  (i{2} <> 0 => 0 < offset{2}) /\

  0 <= offset{2} <= size stack{2} /\

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

  ots_addr{1}.[3] = W32.zero /\
  ltree_addr{1}.[3] = W32.one /\
  node_addr{1}.[3] = W32.of_int 2 /\

  sub ots_addr{1} 0 3 = sub address{2} 0 3 /\ 
  sub ltree_addr{1} 0 3 = sub address{2} 0 3 
); last first.
    + auto => /> &1 &2 *; do split.
        * smt(@W32 pow2_32).
        * smt(pow2_neq_0).
        * smt(pow2_nonnegative).
        * apply (eq_from_nth witness); first by rewrite size_map size_sub_list // size_sub.
          rewrite size_map size_sub // /#.
        * apply (eq_from_nth witness); first by rewrite size_sub // size_sub_list.
          rewrite size_sub // /#.
        * apply (eq_from_nth witness); first by rewrite !size_sub.
          rewrite size_sub // => j?. 
          by rewrite !nth_sub //= /set_type get_setE // ifF 1:/#.
        * apply (eq_from_nth witness); first by rewrite !size_sub.
          rewrite size_sub // => j?. 
          by rewrite !nth_sub //= /set_type get_setE // ifF 1:/#.
        * rewrite ultE /#.
        * rewrite ultE /#.
        * move => stackImpl heightsL i offset heightsR stackR.
          rewrite ultE => ??????H1?????.
          rewrite n_val => H2?. 
          have ?: 0 < to_uint i by smt(pow2_neq_0).
          admit.
(*
          apply (eq_from_nth witness); first by rewrite valP n_val size_sub //.
          move : H2.
          rewrite /sub.
          have ->: 32 * to_uint offset = 32 + 32 * (to_uint offset - 1) by smt().
          rewrite /sub_list !(mkseq_add _ 32) 1..4:/# => H.
          have ->: mkseq (fun (i0 : int) => stackImpl.[0 + i0]) 32 = mkseq (fun (i0 : int) => nth witness (nbytes_flatten stackR) (0 + i0)) 32.
             + have := eqseq_cat (mkseq (fun (i0 : int) => stackImpl.[0 + i0]) 32)
                (mkseq (fun (i0 : int) => nth witness (nbytes_flatten stackR) (0 + i0)) 32) (* 1st argument *)
                (mkseq (fun (i0 : int) => (fun (i1 : int) => stackImpl.[0 + i1]) (32 + i0)) (32 * (to_uint offset - 1))) (* 2nd argument *)
                (mkseq (fun (i0 : int) => (fun (i1 : int) => nth witness (nbytes_flatten stackR) (0 + i1)) (32 + i0)) (32 * (to_uint offset - 1))). (* 3rd argument *)
                     by rewrite !size_mkseq /max //= H //=. 
          rewrite size_mkseq /= => j?.
          rewrite nth_mkseq //= /nbytes_flatten (nth_flatten witness n).
            + pose P := (fun (s0 : W8.t list) => size s0 = n).
              pose L := (map NBytes.val stackR).
              rewrite -(all_nthP P L witness) /P /L size_map H1 d_val h_val /= => k?. 
              by rewrite (nth_map witness) 1:/# valP. 
          by rewrite (nth_map witness) /#.
*)

(*================ O ultimo goal do while termina aqui ====================== *)
 
seq 2 0 : (#pre /\ to_uint t32{1} = s{2} + i{2}).
    + auto => /> &1 &2 *.
      rewrite to_uintD_small //= /#.

wp.

seq 1 0 : (#pre /\ to_uint ltree_addr{1}.[4] = s{2} + i{2}).
    + inline {1}; auto => /> &1 &2 ???????????????????<- *. 
      (* A seta refere se a hipotese sub ltree_addr{1} 0 3 = sub address{2} 0 3 *)
      apply (eq_from_nth witness); first by rewrite !size_sub.
      rewrite size_sub // => j?.
      by rewrite !nth_sub //= get_setE // ifF 1:/#. 

seq 1 0 : (#pre /\ to_uint ots_addr{1}.[4] = s{2} + i{2}).
    + inline {1}.
      auto => /> &1 &2 ??????????????????<- *.
      (* A seta refere se a hipotese sub ots_addr{1} 0 3 = sub address{2} 0 3 *)
      apply (eq_from_nth witness); first by rewrite !size_sub.
      rewrite size_sub // => j?.
      by rewrite !nth_sub //= get_setE // ifF 1:/#.

(* ==================================================================================================================================================== *)
 
seq 1 6 : (#pre /\ to_list buf{1} = val node{2}).
    + inline {1} M(Syscall).__gen_leaf_wots_ M(Syscall)._gen_leaf_wots M(Syscall).__gen_leaf_wots.
      
      seq 22 0 : (
           #pre /\ 
           ots_addr2{1} = ots_addr{1} /\
           sk_seed2{1} = sk_seed{1} /\
           pub_seed2{1} = pub_seed{1} /\
           ltree_addr2{1} =  ltree_addr{1}
      ); first by auto.
          
      seq 0 2 : (
           #{/~ots_addr2{1} = ots_addr1{1}}
            {/~sub ltree_addr{1} 0 3 = sub address{2} 0 3}pre /\ 
 
           sub ltree_addr{1} 0 3 = sub address{2} 0 3 /\
           forall (k : int), 0 <= k < 5 => address{2}.[k] = ots_addr2{1}.[k]
      ).
         * auto => /> &1 &2 ???????????????H2?? H0 H3 ???? H1 *.
           rewrite /set_type /set_ots_addr; do split.
               - apply (eq_from_nth witness); first by rewrite !size_sub.
                 rewrite size_sub // => j?.
                 rewrite !nth_sub //= get_setE // ifF 1:/# get_setE //.
                 case (j = 3) => //?.
                 have ->: ots_addr{1}.[j] = nth witness (sub ots_addr{1} 0 3) j by rewrite nth_sub.
                 by rewrite H0 nth_sub.
               - apply (eq_from_nth witness); first by rewrite !size_sub.
                 rewrite size_sub // => j?.
                 rewrite !nth_sub //= get_setE // ifF 1:/# get_setE // ifF 1:/#.
                 have ->: ltree_addr{1}.[j] = nth witness (sub ltree_addr{1} 0 3) j by rewrite nth_sub /#.
                 rewrite H3 nth_sub // /#.
               - move => k??.
                 rewrite get_setE //.
                 case (k = 4) => [-> |?].
                      + by rewrite -H1 to_uintK.
                 case (k = 3) => [-> |?]. 
                      + by rewrite H2 get_setE.
                 rewrite get_setE // ifF //.
                 have ->: ots_addr{1}.[k] = nth witness (sub ots_addr{1} 0 3) k by rewrite nth_sub /#.
                 rewrite H0 nth_sub /#.

      seq 1 1 : (
          #{/~ots_addr2{1} = ots_addr{1}}
           {/~forall (k : int), 0 <= k && k < 5 => address{2}.[k] = ots_addr2{1}.[k]}pre /\ 
          pk{1} = DecodeWotsPk pk{2}
      ). 
         * exists * sk_seed2{1}, pub_seed2{1}; elim * => P0 P1.
           call (pkgen_correct P0 P1) => [/#|].
           skip => /> /#.
      
      seq 0 2 : (
          #{/~sub ots_addr{1} 0 3 = sub address{2} 0 3}pre /\ 
          forall (k : int), 0 <= k < 5 => ltree_addr2{1}.[k] = address{2}.[k]
      ).

          * auto => /> &1 &2 ??????????????????????H1?H0 *; split => [| k??].
               - apply (eq_from_nth witness); first by rewrite !size_sub.
                 rewrite size_sub // => j?.
                 by rewrite H0 !nth_sub //= /set_tree_addr /set_type get_setE // ifF 1:/# get_setE // ifF 1:/#.
               - rewrite /set_ltree_addr /set_type get_setE //.
                 case (k = 4) => [-> |?].
                      + by rewrite -H1 to_uintK.
                 rewrite get_setE //.
                 case (k = 3) => //?.
                 have ->: ltree_addr{1}.[k] = nth witness (sub ltree_addr{1} 0 3) k by rewrite nth_sub // /#.
                 rewrite H0 nth_sub // /#.

      wp.
      admit.

(* ==================================================================================================================================================== *)

seq 2 0 : (#pre /\ to_uint t64{1} = offset{2} * 32).
          + auto => /> &1 &2 *.
            rewrite to_uintM of_uintK //=/#.

seq 1 1 : #pre.
    + exists * _stack{1}, buf{1}, t64{1}; elim * => P0 P1 P2.
      call {1} (memcpy_u8u8_3_352_32_post P0 P1 P2).
      auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 *; do split.
          - rewrite H26 /#.
          - rewrite h_val d_val /= in H7.
            move: H6; rewrite H7 => H6.
            rewrite H26.  admit. (* Isto e falso *)
          - move => ?? r H; do split.
              * rewrite size_put /#.
              * rewrite size_put /#.
              * apply (eq_from_nth witness); first by rewrite size_sub 1:/# size_sub_list // /#.
                rewrite size_sub 1:/# n_val => j?.
                rewrite nth_sub 1:/# /= /sub_list nth_mkseq //= /nbytes_flatten (nth_flatten witness n).
                     + admit.
                rewrite (nth_map witness).
                     + rewrite size_put /#.
                rewrite nth_put 1:/# ifF 1:/#.
                admit.


seq 2 2 : #{/~to_uint t64{1} = offset{2} * 32}pre.
          + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26; do split.
               * rewrite to_uintD /#.
               * smt().
               * smt().
               * rewrite H7 d_val h_val /=. admit.
               * by rewrite size_put H8.
               * apply (eq_from_nth witness); first by rewrite size_sub_list 1:/# size_map size_sub 1:/#.
                 rewrite size_map size_sub 1:/# => j?.
                 rewrite /sub_list nth_mkseq //= (nth_map witness).
                     + rewrite size_sub /#.
                 rewrite nth_sub // nth_put.
                     + admit.
                 case (to_uint offset{1} = j) => H.
                     + rewrite get_setE /=.
                         * admit. 
                       rewrite ifT //. 
                       smt(@W64 pow2_64).
                     + rewrite get_setE /=.
                         * admit.
                       rewrite ifF 1:#smt:(@W64 pow2_64).
                       have ->: nth witness heights{2} j = nth witness (sub_list heights{2} 0 (to_uint offset{1})) j by rewrite /sub_list nth_mkseq 1:/#.
                       rewrite -H13 (nth_map witness).
                         * rewrite size_sub //#.
                       by rewrite nth_sub 1:/#.
               
               * apply (eq_from_nth witness); first by rewrite size_sub 1:/# size_sub_list /#.
                 rewrite size_sub 1:/# n_val => j?.
                 rewrite nth_sub 1:/# /sub_list nth_mkseq //= /nbytes_flatten (nth_flatten witness n).
                         * pose P := (fun (s0 : W8.t list) => size s0 = n).
                           pose L := (map NBytes.val stack{2}).
                           rewrite -(all_nthP P L witness) /P /L size_map H7 d_val h_val /= => k?. 
                           by rewrite (nth_map witness) 1:/# valP. 
                 rewrite (nth_map witness).
                         * admit.
                 admit.

seq 1 0 : (
    #pre /\ 
    if treehash_cond heights{1} offset{1} then cond{1} = W8.one else cond{1} = W8.zero
).
    + ecall {1} (treehash_cond_correct_p heights{1} offset{1}).
      auto => /> /#.

while (#pre); first by admit.
    + skip => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 *; do split.
         * move => H27.
           have E: treehash_cond heights{1} offset{1}.
              move: H26.
              move: H27. 
           admit.
         * admit. (* Treehash cond needs to be an smequivalence *)
         * move => ?. 
           have ->: nth witness heights{2} (to_uint offset{1} - 1) = nth witness (sub_list heights{2} 0 (to_uint offset{1})) (to_uint offset{1} - 1) by rewrite /sub_list nth_mkseq /#.
           have ->: nth witness heights{2} (to_uint offset{1} - 2) = nth witness (sub_list heights{2} 0 (to_uint offset{1})) (to_uint offset{1} - 2) by rewrite /sub_list nth_mkseq /#.
           rewrite -H13 !(nth_map witness) //=. 
              + rewrite size_sub /#.
              + rewrite size_iota /#.
              + rewrite size_sub /#.
              + rewrite size_iota /#.
           rewrite nth_iota 1:/# nth_iota 1:/# /= => H30.
           have := H26.
           rewrite /treehash_cond ifT; split => [/# |].
           smt(@W32 pow2_32).
         * move => stackImpl bufL heightsImpl node_addr offsetImpl addrSpec heighrsSpec stackSpec.
         * move => H31 H32 H33 H34 H35 H36 H37 H38 H39 H40 H41 H42 H43 H44*; do split.
               - admit.
               - smt().
               - smt().
               - admit.
               - smt(@W32 pow2_32).
               - rewrite ultE; smt(@W32 pow2_32).
               - rewrite ultE; smt(@W32 pow2_32).
qed.

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
      admit.

seq 1 1 : (#pre /\ to_list node{1} = val t{2}).
    + inline {1} 1.
      inline {1} 13.
      wp; sp.
      exists * pub_seed{1}, sk_seed{1}, k{1}, (of_int j{1})%W32, addr{1}.
      elim * => P0 P1 P2 P3 P4.
      call {1} (treehash_correct P1 P0 P2 P3 P4) => [/# |].
      skip => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 ->.
      do split; 1,2:smt(@NBytes).
         * rewrite of_uintK /#.
         * rewrite of_uintK /#.
         * smt(@W32 pow2_32).
         * admit.
         * rewrite of_uintK => *.
           admit.            


auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11; do split; 1,2,5,6: by smt().
    - by rewrite size_put.
    - move => k??.

rewrite initiE 1:/# /= /nbytes_flatten (nth_flatten witness 32).
    + pose P := (fun (s : W8.t list) => size s = 32).
      pose L := (map NBytes.val (put authentication_path{2} j{2} t{2})).
      rewrite -(all_nthP P L witness) /P /L size_map size_put H4 => i?.
      rewrite (nth_map witness); first by rewrite size_put /#.
      by rewrite valP n_val.

rewrite (nth_map witness); first by rewrite size_put /#.
rewrite nth_put 1:/#.

case (j{2} * 32 <= k && k < j{2} * 32 + 32) => ?.
    + rewrite ifT 1:/# -H11 get_to_list /#.
    + rewrite ifF 1:/# H7 1:/# /nbytes_flatten (nth_flatten witness 32).
         - pose P := (fun (s : W8.t list) => size s = 32).
           pose L := (map NBytes.val authentication_path{2}).
           rewrite -(all_nthP P L witness) /P /L size_map => ??.
           by rewrite (nth_map witness) 1:/# valP n_val.
      by rewrite (nth_map witness) 1:/#.
qed.


lemma treesig_correct (_m : W8.t Array32.t, _sk : xmss_sk, _idx_sig : W32.t, _addr : W32.t Array8.t) :
    n = XMSS_N /\
    len = XMSS_WOTS_LEN /\ 
    d = XMSS_D /\
    h = XMSS_TREE_HEIGHT /\ 
    floor (log2 w%r) = XMSS_WOTS_LOG_W /\ 
    w = XMSS_WOTS_W /\ 
    len1 = XMSS_WOTS_LEN1 /\ 
    len2 = XMSS_WOTS_LEN2
 =>
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

      (* Isto e a negacao da condicao idx >= ((1ULL << params->full_height) - 1) usada p verificar se ainda se pode assinat com uma determinada chave *)
      (* FIXME: e 2^XMSS_FULL_HEIGHT - 1 e nao 2^XMSS_FULL_HEIGHT *)
      0 <= to_uint _idx_sig < 2 ^ XMSS_FULL_HEIGHT - 1

      ==>
      res{2} = EncodeReducedSignature (to_list res{1}.`1)
    ].
proof.
rewrite /XMSS_N /XMSS_WOTS_LEN /XMSS_D /XMSS_TREE_HEIGHT /XMSS_WOTS_LOG_W.
rewrite /XMSS_WOTS_W /XMSS_WOTS_LEN1 /XMSS_WOTS_LEN2.
move => [#] n_val len_val d_val h_val logw_val w_val len1_val len2_val.
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
    + auto => /> &1 ?? -> ->; split; rewrite /DecodeSkNoOID.
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
  0 <= to_uint idx_sig{1} < 2 ^ XMSS_FULL_HEIGHT - 1
  ==>
  _
); first by auto.
 
seq 1 1 : (#pre /\ auth{2} = EncodeAuthPath (to_list auth_path{1})).
    + exists * pub_seed{1}, sk_seed{1}, idx_sig{1}, addr{1}.
      elim * => P0 P1 P2 P3.
      call (build_auth_path_correct P0 P1 P2 P3) => [/# |].
      skip => /> &2 <- <- ??; by smt(@NBytes).

seq 2 2 : (#pre); first by inline {1}; auto.

seq 1 1 : (sig_ots{2} = EncodeWotsSignature sig_ots{1} /\ auth{2} = EncodeAuthPath (to_list auth_path{1})).
    + inline {1} M(Syscall).__wots_sign_ M(Syscall)._wots_sign.
      sp; wp.
      exists * msg0{1}, seed0{1}, pub_seed{1}, addr1{1}.
      elim * => P0 P1 P2 P3.
      call {1} (wots_sign_seed_corect P0 P1 P2 P3) => [/# |]. 
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

