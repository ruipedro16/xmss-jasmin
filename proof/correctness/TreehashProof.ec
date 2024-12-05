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
require import Correctness_Hash.
require import Correctness_Mem.
require import Correctness_TreehashCondition.
require import LTReeProof.

require import WArray32.

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

      0 <= to_uint _t <= XMSS_TREE_HEIGHT /\
      0 <= to_uint _s <= to_uint _t /\
      _addr.[4] = W32.zero
      ==>
      to_list res{1} = val res{2}
    ]. 
proof. 
rewrite /XMSS_N /XMSS_D /XMSS_TREE_HEIGHT /XMSS_FULL_HEIGHT /XMSS_D /XMSS_WOTS_W /XMSS_WOTS_LEN /= .
move => [#] n_val d_val h_val tree_height *.
rewrite h_val d_val in tree_height. 
proc => /=.
have E0 : 2 ^ h = 1048576 by rewrite h_val /#.
seq 7 0 : #pre; first by auto. 
seq 4 3 : (
  #pre /\
  offset{1} = W64.zero /\
  ={offset} /\
  ots_addr{1} = subtree_addr{1} /\
  ltree_addr{1} = subtree_addr{1} /\
  node_addr{1} = subtree_addr{1} /\
  node_addr{1}.[4] = W32.zero /\
  address{2}.[4] = W32.zero /\

  size stack{2} = h %/ d + 1 /\      (* = 11 *)
  size heights{2} = h %/ d + 1  /\   (* = 11 *)
  size stack{2} = size heights{2}
).
    + auto => /> ???? H; do split; 5,6: by rewrite size_nseq /#.
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
         * rewrite /get32_direct pack4E wordP => i?.
           rewrite initiE //= initiE 1:/# /= /init64 initiE 1:/# /= /copy_64 initiE 1:/# /=.
           rewrite  get64E pack8E bits8iE 1:/# initiE 1:/# /= initiE 1:/# //= /init32 initiE 1:/# /= bits8iE 1:/#.
           rewrite (: (8 * ((16 + i %/ 8) %/ 8) + ((16 + i %/ 8) %% 8 * 8 + i %% 8) %/ 8) %/ 4 = 4) 1:/# H /#.
         * by rewrite !size_nseq. 

seq 4 0 : (
  #{/~ots_addr{1} = subtree_addr{1}}
   {/~ltree_addr{1} = subtree_addr{1}}
   {/~node_addr{1} = subtree_addr{1}}pre /\
   sub ots_addr{1} 0 3 = sub address{2} 0 3 /\ 
   sub ltree_addr{1} 0 3 = sub address{2} 0 3 /\
   sub node_addr{1} 0 3 = sub address{2} 0 3 /\
   ots_addr{1}.[3] = W32.zero /\
   ltree_addr{1}.[3] = W32.one /\
   node_addr{1}.[3] = W32.of_int 2 /\
   node_addr{1}.[4] = W32.zero
).
    + inline {1}.
      auto => /> *.
      do split; (
          apply (eq_from_nth witness); [by rewrite !size_sub | rewrite size_sub // => ??]; 
          by rewrite !nth_sub //= get_setE // ifF 1:/# 
      ).

swap {1} 1 2.

seq 2 0 : (#pre /\ to_uint upper_bound{1} = 2^t{2}).
    + auto => /> &2 *.
      rewrite (: 31 = 2^5 - 1) 1:/# and_mod // shl_shlw 1:#smt:(@W32) of_uintK to_uint_shl 1:/# /=.
      have ->: to_uint _t %% 32 %% 4294967296 = to_uint _t by smt(modz_small). 
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
      t{2} = to_uint target_height{1} /\ 0 <= t{2} <= h /\
      s{2} = to_uint start_index{1} /\ 0 <= s{2} <= h /\ 

      0 <= to_uint offset{2} /\ 
      ={offset} /\  
      (i{2} <> 0 => 0 < to_uint offset{2}) /\

      0 <= i{2} <= 2^t{2} /\ to_uint i{1} = i{2} /\
      to_uint upper_bound{1} = 2 ^ t{2} /\

      size stack{2} = h %/ d + 1 /\ 
      size heights{2} = h %/ d + 1 /\

      sk_seed{2} = (insubd (to_list sk_seed{1}))%NBytes /\
      pub_seed{2} = (insubd (to_list pub_seed{1}))%NBytes /\ 
      
      sub ots_addr{1} 0 3 = sub address{2} 0 3 /\
      sub ltree_addr{1} 0 3 = sub address{2} 0 3 /\
      sub node_addr{1} 0 3 = sub address{2} 0 3 /\

      ots_addr{1}.[3] = W32.zero /\       (* type *)
      ltree_addr{1}.[3] = W32.one /\      (* type *)
      node_addr{1}.[3] = W32.of_int 2 /\  (* type *)
      node_addr{1}.[4] = W32.zero /\      (* padding *)
      
      sub heights{1} 0 (min (to_uint offset{2}) (size heights{2})) = sub_list heights{2} 0 (min (to_uint offset{2}) (size heights{2})) /\

      sub _stack{1} 0 (n * (min (to_uint offset{2}) (size stack{2}))) = sub_list (nbytes_flatten stack{2}) 0 (n * (min (to_uint offset{2}) (size stack{2})))
); last first.

(* ============================================ last subgoal of the first while loop starts here *)

+ auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 *.
  rewrite pow2_nonnegative //.
  do split; 1,2: by smt().
        * apply (eq_from_nth witness); first by rewrite size_sub 1:/# size_sub_list /#.
          rewrite size_sub /#.
        * apply (eq_from_nth witness); first by rewrite size_sub 1:/# size_sub_list /#.
          rewrite  size_sub /#.
        - rewrite ultE /#.
        - rewrite ultE /#.
        - move => _stack_L heights_L i_L ltree_addr_L node_add_L offset_L ots_addr_L address_R heights_R stack_R.
          rewrite ultE => H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 *.
          apply (eq_from_nth witness); first by rewrite size_sub 1:/# valP n_val.
          rewrite size_sub 1:/# n_val => j?.
          have ?: 0 < to_uint i_L by smt(pow2_neq_0).
          have := H33.
          rewrite /sub /sub_list/XMSS_TREE_HEIGHT n_val /=.
          move => T.
          rewrite nth_mkseq 1:/# /=.
          have ->: _stack_L.[j] = nth witness (mkseq (fun (i0 : int) => _stack_L.[i0]) (32 * min (to_uint heights_R) (size stack_R))) j by rewrite nth_mkseq // 1:/#.
          by rewrite T nth_mkseq 1:/# /= nth_nbytes_flatten /#.

(* ============================================ last subgoal of the first while loop ends here *)

seq 2 0 : (#pre /\ to_uint t32{1} = s{2} + i{2}).
    + auto => /> &1 &2; rewrite ultE => *.
      rewrite to_uintD_small //=. 
      smt(@IntDiv @RealExp).
 
swap {1} 2 -1.

seq 1 2 : (
    #{/~sub ots_addr{1} 0 3 = sub address{2} 0 3}pre /\ sub ots_addr{1} 0 5 = sub address{2} 0 5
).
    + inline {1}; auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22*. 
      rewrite /set_ots_addr /set_type.
      do split; (
         apply (eq_from_nth witness); [by rewrite !size_sub | rewrite size_sub // => j?];
         rewrite !nth_sub //= !get_setE //
      ).
         * do (rewrite ifF 1:/#).
           have ->: ltree_addr{1}.[j] = nth witness (sub ltree_addr{1} 0 3) j by rewrite nth_sub.
           by rewrite H12 nth_sub.
         * do (rewrite ifF 1:/#).
           have ->: node_addr{1}.[j] = nth witness (sub node_addr{1} 0 3) j by rewrite nth_sub.
           by rewrite H13 nth_sub.
         * case (j = 4) => ?.
              - smt(@W32 pow2_32).
              - do 3! (rewrite ifF 1:/#).
                case (j = 3) => [/# |?].
                have ->: ots_addr{1}.[j] = nth witness (sub ots_addr{1} 0 3) j by rewrite nth_sub /#.
                rewrite H11 nth_sub /#.

wp.

seq 1 0 : (#pre /\ ltree_addr{1}.[4] = W32.of_int (s{2} + i{2})).
    + inline {1}; auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22*.
      split.
         * apply (eq_from_nth witness); first by rewrite !size_sub.
           rewrite size_sub // => i?.
           rewrite !nth_sub // get_setE // ifF 1:/# /=.
           have ->: ltree_addr{1}.[i] = nth witness (sub ltree_addr{1} 0 3) i by rewrite nth_sub.
           by rewrite H11 nth_sub.
         * by rewrite -H21 to_uintK.

seq 1 4 : (
  #{/~sub ots_addr{1} 0 5 = sub address{2} 0 5}
   {/~ltree_addr{1}.[4] = (of_int (s{2} + i{2}))%W32}pre /\
   val node{2} = to_list buf{1} /\ 
   sub ots_addr{1} 0 3 = sub address{2} 0 3
).

(* ================================================== proof for gen leaf starts here =================================================================== *)

inline {1} M(Syscall).__gen_leaf_wots_ M(Syscall)._gen_leaf_wots M(Syscall).__gen_leaf_wots.             

seq 22 0 : (
    #pre /\
  sk_seed2{1} = sk_seed{1} /\
  pub_seed2{1} = pub_seed{1} /\
  ots_addr2{1} = ots_addr{1} /\
  ltree_addr2{1} = ltree_addr{1}
); first by auto.

seq 1 1 : (
        #{/~ots_addr2{1} = ots_addr{1}}pre /\ 
        pk{1} = DecodeWotsPk pk{2} /\
        ots_addr2{1}.[0] = address{2}.[0] /\
        ots_addr2{1}.[1] = address{2}.[1] /\
        ots_addr2{1}.[2] = address{2}.[2] /\
        ots_addr2{1}.[3] = W32.zero 
).
         * exists * sk_seed2{1}, pub_seed2{1}, ots_addr2{1}, address{2}.
           elim * => P3 P4 P5 P6.
           call {1} (pkgen_correct P3 P4 P5 P6) => [/# |].
           auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 resL resR H27 H28*.
           do split; [
               have ->: P6.[0] = nth witness (sub P6 0 5) 0 by rewrite nth_sub | 
               have ->: P6.[1] = nth witness (sub P6 0 5) 1 by rewrite nth_sub |     
               have ->: P6.[2] = nth witness (sub P6 0 5) 2 by rewrite nth_sub |
           ]; 1..3: by rewrite -H24 -H28 nth_sub /#.        
           have ->: resL.`2.[3] = nth witness (sub resL.`2 0 5) 3 by rewrite nth_sub /#.
           by rewrite H28 nth_sub.

seq 0 2 : (
          #{/~sub ots_addr{1} 0 5 = sub address{2} 0 5}pre /\ 
          sub ltree_addr2{1} 0 5 = sub address{2} 0 5
      ).
         * auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27*.
           rewrite /set_ltree_addr /set_type.
           do split; (
              apply (eq_from_nth witness); [by rewrite !size_sub | rewrite size_sub // => i?];
              rewrite !nth_sub // !get_setE //=
           ).
               - do (rewrite ifF 1:/#).
                 have ->: ltree_addr{1}.[i] = nth witness (sub ltree_addr{1} 0 3) i by rewrite nth_sub.
                 by rewrite H11 nth_sub.
               - do (rewrite ifF 1:/#).
                 have ->: node_addr{1}.[i] = nth witness (sub node_addr{1} 0 3) i by rewrite nth_sub.
                 by rewrite H12 nth_sub.
               - case (i = 4) => [-> /# |?].
                 case (i = 3) => [-> /# |?].
                 do (rewrite ifF 1:/#).
                 have ->: ltree_addr{1}.[i] = nth witness (sub ltree_addr{1} 0 3) i by rewrite nth_sub /#.
                 by rewrite H11 nth_sub /#.

seq 1 1 : (
          #{/~ltree_addr2{1} = ltree_addr{1}}pre /\ 
          to_list leaf1{1} = val node{2} /\
          ltree_addr2{1}.[0] = address{2}.[0] /\
          ltree_addr2{1}.[1] = address{2}.[1] /\
          ltree_addr2{1}.[2] = address{2}.[2] /\
          ltree_addr2{1}.[3] = W32.one
      ).
         * exists * pk{1}, ltree_addr2{1}, pub_seed2{1}.
           elim * => P0 P1 P2.
           call (ltree_correct P0 P2 P1) => [/# |].
           auto => /> &1 &2 *; split; [apply enc_dec_wots_pk => /# | smt(addr_sub_5)].

auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32*.
      do split.
         * apply (eq_from_nth witness); first by rewrite !size_sub.
           rewrite size_sub // => i?. 
           rewrite !nth_sub /#.
         * by rewrite H28.
         * apply (eq_from_nth witness); first by rewrite !size_sub.
           rewrite size_sub // => i?. 
           rewrite !nth_sub /#.

(* ================================================== proof for gen leaf ends here =================================================================== *)
  
seq 2 0 : (#pre /\ t64{1} = offset{2} * W64.of_int 32); first by auto.

seq 3 3 : (#{/~ t64{1} = offset{2} * W64.of_int 32}pre); last by admit.
          + inline {1}; wp.
            conseq />.
            sp.
            case (to_uint offset{2} <= size heights{2}); first by admit.
(* =========================================================================== *)
            while {1} 
            (bytes{1} = 32 /\
             aux0{1} = bytes{1} /\
             0 <= i0{1} <= aux0{1} /\
             out_offset{1} = t64{1} /\ 
             t64{1} = offset{2} * W64.of_int 32 /\
             ={offset} /\
             size stack{2} = h %/ d + 1 /\
             size heights{2} = h %/ d + 1 /\
             (i{2} <> 0 => 0 < to_uint offset{2}) /\
             (forall (k : int), 0 <= k < i0{1} => out{1}.[to_uint (out_offset{1} + (of_int k)%W64)] = in_0{1}.[k]) /\
             (forall (k : int), 0 <= k <= to_uint out_offset{1} => out{1}.[k] = nth witness (nbytes_flatten stack{2}) k) /\
             (forall (k : int), to_uint (out_offset{1} + (of_int k)%W64) <= k < size (nbytes_flatten stack{2}) => out{1}.[k] = nth witness (nbytes_flatten stack{2}) k)
            )
            (32 - i0{1}); first by admit.
                * auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23  *.
                  have E1:  (min (to_uint offset{2}) (size heights{2})) = size heights{2} by smt().
                  do split.
                     - smt(). 
                     - admit.        
                     - move => k?.
                       rewrite size_nbytes_flatten n_val => ?.
                       admit.
                     - move => i0L outL; do split.
                          + move => ??.
                            


(* =========================================================================== *)
            while {1} 
            (bytes{1} = 32 /\
             aux0{1} = bytes{1} /\
             0 <= i0{1} <= aux0{1} /\
             out_offset{1} = t64{1} /\ 
             t64{1} = offset{2} * W64.of_int 32 /\
             ={offset} /\
             0 <= to_uint offset{2} < size heights{2} /\
             size stack{2} = h %/ d + 1 /\
             size heights{2} = h %/ d + 1 /\
             (i{2} <> 0 => 0 < to_uint offset{2}) /\
             (forall (k : int), 0 <= k < i0{1} => out{1}.[to_uint (out_offset{1} + (of_int k)%W64)] = in_0{1}.[k]) /\
             (forall (k : int), 0 <= k <= to_uint out_offset{1} => out{1}.[k] = nth witness (nbytes_flatten stack{2}) k) /\
             (forall (k : int), to_uint (out_offset{1} + (of_int k)%W64) <= k < size (nbytes_flatten stack{2}) => out{1}.[k] = nth witness (nbytes_flatten stack{2}) k)
            )
            (32 - i0{1}); first by admit.
                * auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 *.
                  have E1 :  (min (to_uint offset{2}) (size heights{2})) = to_uint offset{2} by smt().






                  split; last by admit.
                  split => [/# |].
                  move => i0L outL.
                  split => [/# |].XS
                  move => ???.
                  have ->: i0L = 32 by smt().
                  move => H.
                  rewrite !size_put.
                  do split => //.
                      - rewrite to_uintD /#.
                      - smt(@W64 pow2_64).
                      - apply (eq_from_nth witness).  
                             + rewrite size_sub; first by smt(@W64 pow2_64). 
                               rewrite size_sub_list; first by smt(@W64 pow2_64).
                               reflexivity.
                        rewrite size_sub; first by smt(@W64 pow2_64).
                        move => j?.
                        rewrite nth_sub // /sub_list nth_mkseq //= nth_put; first by smt(@W64 pow2_64).
                        have ->: to_uint (offset{2} + W64.one - W64.one) = to_uint offset{2} by smt(@W64 pow2_64).
                        rewrite get_setE; first by smt(@W64 pow2_64).
                        case (j = to_uint offset{2}) => ?; first by rewrite ifT /#.
                        rewrite ifF 1:/#.
                        have ->: heights{1}.[j] = nth witness (sub heights{1} 0 (min (to_uint offset{2}) (size heights{2}))) j by rewrite E1 nth_sub 2:/#; smt(@W64 pow2_64).
                        rewrite H17.
                        by rewrite /sub_list nth_mkseq // E1; smt(@W64 pow2_64).
                      - apply (eq_from_nth witness). 
                             + rewrite size_sub; first by smt(@W64 pow2_64). 
                               rewrite size_sub_list; first by smt(@W64 pow2_64).
                               reflexivity.
                        rewrite size_sub; first by smt(@W64 pow2_64). 
                        move => j Hj.                        
                        rewrite nth_sub //= /sub_list nth_mkseq //=.
                        rewrite nth_nbytes_flatten; first by rewrite size_put; smt(@W64 pow2_64).
                        rewrite nth_put 1:/#.
                        case (to_uint offset{2} = j %/ n) => Ha; first by admit.
                             + 


                             + rewrite H22 get_to_list.
                               have E2: sub outL (to_uint offset{2} * 32) 32 = to_list buf{1}.
                                    - apply (eq_from_nth witness); first by rewrite size_to_list size_sub.
                                      rewrite size_sub // => k?.
                                      rewrite get_to_list -H // nth_sub //.
                                      by congr; smt(@W64 pow2_64).
                               have ->: outL.[j] = nth witness (sub outL (to_uint offset{2} * 32) 32) (j - 32 * to_uint offset{2}) by rewrite nth_sub 1:/#; congr; smt(@W64 pow2_64).
                               rewrite E2 get_to_list /#.




                * auto => /> &hr ???????Ha?. 
                  do split; 1,2,4: by smt().
                  move => k??.
                  rewrite get_setE; first by smt(@W64 pow2_64).
                  case (k = i0{hr}) => [-> /=// | ?]. 
                  rewrite ifF; first by smt(@W64 pow2_64).
                  apply Ha => /#.
               

 
 
            admit.
 
seq 1 0 : (
    #pre /\ 
    (cond{1} = W8.one) = 
    (W64.of_int 2 \ule offset{2} /\ heights{1}.[to_uint (offset{1} - W64.of_int 2)] = heights{1}.[to_uint (offset{1} - W64.one)])
); first by  ecall {1} (p_treehash_condition_correct_eq heights{1} offset{1}); auto.
   
seq 0 1 : (#pre /\ sub node_addr{1} 0 5 = sub address{2} 0 5).
    + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 *.
      rewrite /set_type.
      do split; (apply (eq_from_nth witness); [by rewrite !size_sub| rewrite size_sub // => i?]; rewrite !nth_sub //= !get_setE //).
         - do (rewrite ifF 1:/#).
           have ->: ltree_addr{1}.[i] = nth witness (sub ltree_addr{1} 0 3) i by rewrite nth_sub.
           by rewrite H11 nth_sub.
         - do (rewrite ifF 1:/#).
           have ->: node_addr{1}.[i] = nth witness (sub node_addr{1} 0 3) i by rewrite nth_sub.
           by rewrite H12 nth_sub.
         - do (rewrite ifF 1:/#).
           have ->: ots_addr{1}.[i] = nth witness (sub ots_addr{1} 0 3) i by rewrite nth_sub.
           by rewrite H23 nth_sub.
         - case (i = 3) => //?. 
           case (i = 4) => //?.
           do (rewrite ifF 1:/#).
           have ->: node_addr{1}.[i] = nth witness (sub node_addr{1} 0 3) i by rewrite nth_sub /#.
           by rewrite H12 nth_sub /#.

conseq />.  (* simplifies #post *)
     
while (
  t{2} = to_uint target_height{1} /\
  0 <= t{2} <= h /\

  s{2} = to_uint start_index{1} /\
  0 <= s{2} <= h /\

  ={offset} /\
  (i{2} <> 0 => 0 < to_uint offset{2}) /\
  0 <= i{2} <= 2 ^ t{2} /\
  to_uint i{1} = i{2} /\
  to_uint upper_bound{1} = 2 ^ t{2} /\

  size stack{2} = h %/ d + 1 /\
  size heights{2} = h %/ d + 1 /\

  sk_seed{2} = (insubd (to_list sk_seed{1}))%NBytes /\
  pub_seed{2} = (insubd (to_list pub_seed{1}))%NBytes /\

  sub ltree_addr{1} 0 3 = sub address{2} 0 3 /\
  sub node_addr{1} 0 5 = sub address{2} 0 5 /\
  sub ots_addr{1} 0 3 = sub address{2} 0 3 /\
  
  ots_addr{1}.[3] = W32.zero /\
  ltree_addr{1}.[3] = W32.one /\
  node_addr{1}.[3] = (of_int 2)%W32 /\
  node_addr{1}.[4] = W32.zero /\

  sub heights{1} 0 (min (to_uint offset{2}) (size heights{2})) = sub_list heights{2} 0 (min (to_uint offset{2}) (size heights{2})) /\
  sub _stack{1} 0 (n * (min (to_uint offset{2}) (size stack{2}))) = sub_list (nbytes_flatten stack{2}) 0 (n * (min (to_uint offset{2}) (size stack{2}))) /\

  i{2} < 2 ^ t{2} /\
  
  (cond{1} = W8.one) = 
    (W64.of_int 2 \ule offset{2} /\ heights{1}.[to_uint (offset{1} - W64.of_int 2)] = heights{1}.[to_uint (offset{1} - W64.one)]) /\

  0 <= to_uint offset{2}
); last by admit.

(* =============================================================================================================================================== *)

seq 2 0 : (#pre /\ tree_idx{1} = (of_int (s{2} + i{2}))%W32).
    + auto => /> &1 &2 *; smt(@W32 pow2_32).

seq 2 0 : (#pre /\ u{1} = (nth witness heights{2} (to_uint (offset{2} - W64.one)) + W32.one)).
    + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23. 
      congr.
      case (to_uint offset{2} <= size heights{2}) => H.
          - (* In this case (min offset (size heights)) = offset *)
            have E1 : min (to_uint offset{2}) (size stack{2}) = to_uint offset{2} by smt().
            have E2 : size stack{2} = size heights{2} by smt().
            have ->: heights{1}.[to_uint (offset{2} - W64.one)] = 
                     nth witness (sub heights{1} 0 (min (to_uint offset{2}) (size heights{2}))) (to_uint (offset{2} - W64.one)).      
               + rewrite nth_sub 2:/#. 
                 split => [| ?]; first by smt(@W64 pow2_64). 
                 rewrite -E2 E1. 
                 smt(@W64 pow2_64). 
            rewrite H17. 
            rewrite -E2 E1 /sub_list nth_mkseq 2:/#.
            smt(@W64 pow2_64).
          - (* In this case (min offset (size heights)) = size heights *)
            have E1 : min (to_uint offset{2}) (size stack{2}) = size stack{2} by smt().
            have E2 : size stack{2} = size heights{2} by smt().
            rewrite nth_out; first by smt(@W64 pow2_64).
            rewrite get_out; first by smt(@W64 pow2_64).
            reflexivity.
  
seq 1 1 : (
    #{/~tree_idx{1} = (of_int (s{2} + i{2}))%W32}pre /\ 
    tree_idx{1} = tree_index{2}
); first by auto.

seq 2 2 : (#pre /\ sub node_addr{1} 0 7 = sub address{2} 0 7).
    + inline{1}. 
      auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23.
      rewrite /set_tree_index /set_tree_height.
      do split; (
           apply (eq_from_nth witness); [by rewrite !size_sub | rewrite size_sub // => i?];
           rewrite !nth_sub //= !get_setE //
      ); 1..3: by do (rewrite ifF 1:/#); smt(sub_k).
      case (i = 6) => //?. 
      case (i = 5) => ?; last by smt(sub_k).
      case (to_uint offset{2} <= size heights{2}) => H.
          - (* In this case (min offset (size heights)) = offset *)
            have E1 : min (to_uint offset{2}) (size stack{2}) = to_uint offset{2} by smt().
            have E2 : size stack{2} = size heights{2} by smt().
            have ->: heights{1}.[to_uint (offset{2} - W64.one)] = nth witness (sub heights{1} 0 (min (to_uint offset{2}) (size heights{2}))) (to_uint (offset{2} - W64.one)).      
               + rewrite nth_sub 2:/#. 
                 split => [| ?]; first by smt(@W64 pow2_64). 
                 rewrite -E2 E1. 
                 smt(@W64 pow2_64). 
            rewrite H17. 
            rewrite -E2 E1 /sub_list nth_mkseq 2:/#.
            smt(@W64 pow2_64).
          - (* In this case (min offset (size heights)) = size heights *)
            have E1 : min (to_uint offset{2}) (size stack{2}) = size stack{2} by smt().
            have E2 : size stack{2} = size heights{2} by smt().
            rewrite nth_out; first by smt(@W64 pow2_64).
            rewrite get_out; first by smt(@W64 pow2_64).
            reflexivity.

seq 4 2 : (#pre /\ to_list buf2{1} = val node0{2} ++ val node1{2}).
          + inline {1}.
            case (to_uint offset{2} <= size heights{2}); last by admit.
                 wp; sp; conseq />.
                 while {1} 
                 (
                   to_uint bytes{1} = 64 /\
                   0 <= to_uint i0{1} <= 64 /\
                   in_0{1} = _stack{1} /\
                   in_offset{1} = t64{1} /\
                   t64{1} = (offset{1} - (of_int 2)%W64) * (of_int 32)%W64 /\
                   sub _stack{1} 0 (n * min (to_uint offset{2}) (size stack{2})) = sub_list (nbytes_flatten stack{2}) 0 (n * min (to_uint offset{2}) (size stack{2})) /\
                   forall (k : int), 0 <= k < to_uint i0{1} => out{1}.[k] = in_0{1}.[to_uint in_offset{1}]
                 )
                 (64 - to_uint i0{1}); first by admit.
                      - auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25. 
                        have E1 : min (to_uint offset{2}) (size stack{2}) = to_uint offset{2} by smt().
                        have E2 : size stack{2} = size heights{2} by smt().
                        split => [/# |].
                        move => i0L outL.
                        rewrite ultE.
                        split => [/# |].
                        rewrite of_uintK  /= => ???.
                        rewrite (: to_uint i0L = 64) 1:/# => H.
                        apply (eq_from_nth witness); first by rewrite size_cat !valP n_val size_to_list.
                        rewrite size_to_list => j?.
                        rewrite get_to_list H //.
                        case (0 <= j < 32) => ?.
                            * rewrite nth_cat !valP n_val ifT 1:/#. 
                              have ->: _stack{1}.[to_uint ((offset{2} - (of_int 2)%W64) * (of_int 32)%W64)] = 
                                       nth witness (sub _stack{1} 0 (n * min (to_uint offset{2}) (size stack{2}))) (to_uint ((offset{2} - (of_int 2)%W64) * (of_int 32)%W64)) 
                                       by rewrite E1 n_val nth_sub /=; smt(@W64 pow2_64).
                              rewrite H18 E1 n_val /sub_list nth_mkseq /=; first by smt(@W64 pow2_64). 
                              admit.
                            * admit.

 
seq 1 1 : (#pre /\ to_list buf{1} = val new_node{2}).
          + inline M(Syscall).__thash_h_ M(Syscall)._thash_h.
            wp; sp.
            exists * node0{2}, node1{2}, pub_seed1{1}, addr0{1}, address{2}.
            elim * => P0 P1 P2 P3 P4.
            call (rand_hash_results P0 P1 P2 P3 P4) => [/# |].
            auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 *.
            do split. 
                 - rewrite /merge_nbytes_to_array tP => i?.
                   rewrite -get_to_list H25 initiE // nth_cat valP n_val.
                   case (0 <= i < 32) => ?; [by rewrite ifT 1:/# ifT 1:/# | by  rewrite ifF 1:/# ifF 1:/#].
                 - smt(sub_k).           
                 - move => ?? resL resR ? H.
                   do split; [| smt() | smt() |]; (
                            apply (eq_from_nth witness); [by rewrite !size_sub | rewrite size_sub // => j?]
                   ); [rewrite -H11 | rewrite -H24]; rewrite !nth_sub //=/#.
 
ecall {1} (p_treehash_condition_correct_eq heights{1} offset{1}).

conseq /> => [/# |].
 
seq 5 2 : #pre; first by admit.
    + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 t_cond H28.
      rewrite !size_put.
      do split => //; 2..4: by admit.
          * apply (eq_from_nth witness); first by rewrite size_sub 1:/# size_sub_list /#.
            rewrite size_sub 1:/# => j Hj.
            case (to_uint offset{2} <= size heights{2}) => ?.
                - have E1: min (to_uint offset{2}) (size heights{2}) = to_uint offset{2} by smt().
                  rewrite E1 nth_sub 1:/# /= /sub_list nth_mkseq 1:/# /=.
                  rewrite get_setE; first by smt(@W64 pow2_64).
                  rewrite nth_put; first by smt(@W64 pow2_64).
                  case (j = to_uint (offset{2} - W64.one)) => ?; [rewrite ifT 1:/#; congr | rewrite ifF 1:/#].
                     * have ->: heights{1}.[to_uint (offset{2} - W64.one)] = 
                                nth witness (sub heights{1} 0 (min (to_uint offset{2}) (size heights{2}))) (to_uint (offset{2} - W64.one))
                                by rewrite E1 nth_sub /#.
                       rewrite H17 /sub_list nth_mkseq /#.  
                     * have ->: heights{1}.[j] = nth witness (sub heights{1} 0 (min (to_uint offset{2}) (size heights{2}))) j by rewrite E1 nth_sub /#.
                       rewrite H17 /sub_list nth_mkseq /#.
                - have E1: min (to_uint offset{2}) (size heights{2}) = size heights{2} by smt().
                  rewrite E1.
                  move: Hj; rewrite E1; move => Hj.
                  rewrite get_out; first by smt(@W64 pow2_64).
                  have ->: nth witness heights{2} (to_uint (offset{2} - W64.one)) = witness by rewrite nth_out /=; smt(@W64 pow2_64).
                  rewrite /sub_list !nth_mkseq //=.
                  rewrite nth_put. admit.













last first. 
    + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 -> H25 *.
      do split.   
        * move => [Ha Hb].
          split; first by assumption.
          have ->: nth witness heights{2} (to_uint (offset{2} - W64.one)) = nth witness (sub_list heights{2} 0 (to_uint offset{1})) (to_uint (offset{2} - W64.one)).
            - rewrite /sub_list.
              case ((0 <= to_uint (offset{2} - W64.one) /\ to_uint (offset{2} - W64.one) < size heights{2})) => H; last by admit.
                 + rewrite nth_mkseq /= 1:/#. /#.


by rewrite /sub_list nth_mkseq /#.
          have ->: nth witness heights{2} (to_uint offset{1} - 1) = nth witness (sub_list heights{2} 0 (to_uint offset{1})) (to_uint offset{1} - 1) by rewrite /sub_list nth_mkseq /#. 
          rewrite -H16.
          rewrite (nth_map witness); first by rewrite size_sub /#.
          rewrite nth_sub 1:/# /= -Hb.
          rewrite (nth_map witness); first by rewrite size_sub /#.
          by rewrite nth_sub 1:/#.
        * move => ?.
          have ->: nth witness heights{2} (to_uint offset{1} - 2) = nth witness (sub_list heights{2} 0 (to_uint offset{1})) (to_uint offset{1} - 2) by rewrite /sub_list nth_mkseq /#.
          have ->: nth witness heights{2} (to_uint offset{1} - 1) = nth witness (sub_list heights{2} 0 (to_uint offset{1})) (to_uint offset{1} - 1) by rewrite /sub_list nth_mkseq /#.
          rewrite -H16.
          rewrite (nth_map witness); first by rewrite size_sub /#.
          rewrite  nth_sub 1:/# /=.
          rewrite (nth_map witness); first by rewrite size_sub /#.
          rewrite  nth_sub 1:/# /= => ?.
          smt(@W32 pow2_32).
        * move => _stack_L cond_L heights_L node_addr_L offset_L address_R heights_R stack_R.
          move => H28 H29 H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 H40 H41 *.
          have E1 : 2 ^ to_uint target_height{1} <= 2^h by smt(@RealExp).
          have E2 : to_uint i{1} <= 2^h by smt(@RealExp).
          rewrite E0 in E2.
          do split. 
            * have E29: (to_uint offset_L <= 2) \/ (nth witness heights_R (to_uint offset_L - 1) <> nth witness heights_R (to_uint offset_L - 2)) by smt().
              have := E29.
              move => [? | ?/#].



              rewrite H32 h_val d_val /= in H43. 

            * smt(). 
            * move => ?. rewrite H32 h_val d_val /=. 
              have E29: (to_uint offset_L <= 2) \/ (nth witness heights_R (to_uint offset_L - 1) <> nth witness heights_R (to_uint offset_L - 2)) by smt().
              have := E29.
              move => [? /# | ?].
              rewrite H32 h_val d_val /= in H43. 
             admit. (* 0 <= to_uint offset_L => to_uint offset_L < size heights_R *)
            * smt().
            * smt().
            * rewrite to_uintD /#.
            * smt(sub_N).
            * smt().
            * rewrite ultE to_uintD /#.
            * rewrite ultE to_uintD /#.

seq 2 0 : (#pre /\ to_uint tree_idx{1} = s{2} + i{2}).
    + auto => /> &1 *. 
      have ?: 0 <= 2 ^ to_uint target_height{1} <= 1048576 by smt(@RealExp).
      rewrite to_uintD_small // /#.

seq 2 0 : (#pre /\ to_uint u{1} = nth witness heights{2} (offset{2} - 1) + 1).
    + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26.
      have ->: nth witness heights{2} (to_uint offset{1} - 1) = nth witness (sub_list heights{2} 0 (to_uint offset{1})) (to_uint offset{1} - 1) by rewrite /sub_list nth_mkseq /#.
      rewrite -H17.
      rewrite (nth_map witness); first by rewrite size_sub /#.
      rewrite nth_sub 1:/# /=.
      have ->: to_uint (offset{1} - W64.one) = to_uint offset{1} - 1 by rewrite to_uintB // uleE /#.
      rewrite to_uintD_small //=.
      have ->: to_uint heights{1}.[to_uint offset{1} - 1] = nth witness (map W32.to_uint (sub heights{1} 0 (to_uint offset{1}))) (to_uint offset{1} - 1).
          *  rewrite (nth_map witness); [by rewrite size_sub /# | by rewrite nth_sub /#]. 
      rewrite H17 (nth_map witness); first by rewrite size_iota /#.
      rewrite /= nth_iota 1:/# /=.
      smt(@W32 pow2_32).

seq 1 1 : (#{/~to_uint tree_idx{1} = s{2} + i{2}}pre /\ tree_idx{1} = tree_index{2}).
    + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27.
      rewrite (: 31 = 2^5 - 1) 1:/# and_mod //.
      rewrite /(`>>`) to_uint_truncateu8 of_uintK modz_small #smt:(@W32 @W8 @IntDiv). 

seq 2 2 : (
    #{/~sub node_addr{1} 0 3 = sub address{2} 0 3}{~sub node_addr{1} 0 4 = sub address{2} 0 4}pre /\ 
    sub node_addr{1} 0 7 = sub address{2} 0 7
).
    + inline {1}.
      auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26*.
      rewrite /set_tree_index /set_tree_height.
      do split; (
         apply (eq_from_nth witness); [by rewrite !size_sub | rewrite size_sub // => i?]; 
         rewrite !nth_sub // !get_setE //=
      ); 1..3:smt(sub_k sub_N).
         - case (i = 6) => //?.
           case (i = 5) => //?.
             + have ->: heights{1}.[to_uint (offset{1} - W64.one)] = W32.of_int (nth witness (map W32.to_uint (sub heights{1} 0 (to_uint offset{1}))) (to_uint offset{1} - 1)).
                   - rewrite (nth_map witness); first by rewrite size_sub /#. 
                     rewrite nth_sub 1:/# /=. 
                     congr.
                     by rewrite to_uintB // uleE /#.    
               congr; rewrite H17 /sub_list nth_mkseq /#. 
           have ->: node_addr{1}.[i] = nth witness (sub node_addr{1} 0 5) i by rewrite nth_sub /#.                    
           rewrite H11 nth_sub /#.              

conseq /> => [/# |].

seq 4 2 : (#pre /\ to_list buf2{1} = val node0{2} ++ val node1{2}).
        + ecall {1} (memcpy_u8u8_2_64_352_post buf2{1} _stack{1} t64{1}).
          auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 result ->.
          apply (eq_from_nth witness); first by rewrite size_sub // size_cat !valP n_val.
          rewrite size_sub // => j?.
          case (0 <= j < 32) => ?; last first.
             - rewrite nth_sub // nth_cat valP ifF 1:/#.
               have ->: to_uint ((offset{1} - (of_int 2)%W64) * (of_int 32)%W64) + j = (to_uint offset{1} - 2) * 32 + j.
                   + rewrite to_uintM of_uintK /= to_uintB; first by rewrite uleE /#.
                     rewrite of_uintK /#.
               have ->: _stack{1}.[(to_uint offset{1} - 2) * 32 + j] = nth witness (sub _stack{1} 0 (n * to_uint offset{1})) ((to_uint offset{1} - 2) * 32 + j) by rewrite nth_sub /#.
               rewrite H19.
               rewrite /sub_list nth_mkseq 1:/# /= nth_nbytes_flatten /#.
             - rewrite nth_sub // nth_cat valP ifT 1:/#.
               have ->: to_uint ((offset{1} - (of_int 2)%W64) * (of_int 32)%W64) + j = (to_uint offset{1} - 2) * 32 + j.
                   + rewrite to_uintM of_uintK /= to_uintB; first by rewrite uleE /#.
                     rewrite of_uintK /#.
               have ->: _stack{1}.[(to_uint offset{1} - 2) * 32 + j] = nth witness (sub _stack{1} 0 (n * to_uint offset{1})) ((to_uint offset{1} - 2) * 32 + j) by rewrite nth_sub /#.
               rewrite H19.
               rewrite /sub_list nth_mkseq 1:/# /= nth_nbytes_flatten /#.
 
seq 1 1 : (#{/~val node{2} = to_list buf{1}}pre /\ to_list buf{1} = val new_node{2}).
          + inline {1} M(Syscall).__thash_h_ M(Syscall)._thash_h.
            wp; sp.
            exists * node0{2}, node1{2}, pub_seed1{1}, addr0{1}, address{2} .
            elim * => P0 P1 P2 P3 P4.
            call (rand_hash_results P0 P1 P2 P3 P4) => [/# |].
            auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28.
            do split.
              - smt(merge_nbytes_val).
              - smt(sub_k).
              - move => H29 H30 resultL resultR H31 H32.
                do split; [| smt() | smt() |]; (
                     apply (eq_from_nth witness); [by rewrite !size_sub | rewrite size_sub // => i?];
                    rewrite !nth_sub //=/#
                ).

ecall {1} (p_treehash_condition_correct_eq heights{1} offset{1}).
wp.
ecall {1} (memcpy_u8u8_3_352_32_post _stack{1} buf{1} t64{1}).
auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29. 
do split; 1,2: by rewrite to_uintM of_uintK /= to_uintB; [by rewrite uleE /# | by rewrite of_uintK /= /#].
move => H30 H31 resultStack H32 H33 H34*.
do split; 1,2: by rewrite to_uintB 2:/# uleE /#.
rewrite !size_put.
have ->: to_uint (offset{1} - W64.one) = to_uint offset{1} - 1 by rewrite to_uintB // uleE /#.
move  => ?? result_cond Hcond. 
have E1: forall (k : int), 0 <= k < to_uint offset{1} => to_uint heights{1}.[k] = nth witness heights{2} k.
   + move => k?.
     have ->: nth witness heights{2} k = nth witness (sub_list heights{2} 0 (to_uint offset{1})) k by rewrite /sub_list nth_mkseq /#.
     rewrite -H17 (nth_map witness); [by rewrite size_sub /# | by rewrite nth_sub /#].
have E2: forall (k : int), 0 <= k < to_uint offset{1} => 0 <= to_uint heights{1}.[k] <= XMSS_TREE_HEIGHT by smt().         
do split => //; 1,6,7: by smt(). (* trivial solves two goals: 12 vs 10 subgoals *)
   + apply (eq_from_nth witness); first by rewrite size_map size_sub_list 1:/# size_sub /#. 
     rewrite size_map size_sub 1:/# => i?.
     rewrite /sub_list nth_mkseq 1:/# /= nth_put 1:/#.
     rewrite (nth_map witness); first by rewrite size_sub /#.     
     rewrite nth_sub 1:/# /= get_setE.
       * rewrite to_uintB; first by rewrite uleE to_uintB 2:/# uleE /#.
         rewrite /= to_uintB 2:/# uleE /#.
     case (i = to_uint offset{1} - 2) => [-> |?].
       * rewrite ifT; first by rewrite to_uintB; [by rewrite uleE to_uintB 2:/# uleE /# | by rewrite /= to_uintB 2:/# uleE /#].
         have ->: to_uint (offset{1} - W64.one - W64.one) = to_uint offset{1} - 2 by rewrite to_uintB; [by rewrite uleE to_uintB 2:/# uleE /# | by rewrite /= to_uintB 2:/# uleE /#].
         rewrite ifT // to_uintD_small 1:/# E1 /#.
       * have ->: to_uint (offset{1} - W64.one - W64.one) = to_uint offset{1} - 2 by rewrite to_uintB; [by rewrite uleE to_uintB 2:/# uleE /# | by rewrite /= to_uintB 2:/# uleE /#].
         rewrite ifF 1:/# ifF 1:/# /#.
   + move => k??.     
     split; [rewrite nth_put /# |]. 
     rewrite !nth_put 1:/#.
     case (k = to_uint offset{1} - 2) => H; last by rewrite ifF /#.
     rewrite ifT 1:/# => ?.

     admit. (* Range das heights *)


   + apply (eq_from_nth witness); first by rewrite size_sub 1:/# size_sub_list /#.
     rewrite size_sub 1:/# => j?.
     rewrite nth_sub 1:/# /= /sub_list nth_mkseq 1:/# /= nth_nbytes_flatten; first by rewrite size_put /#.
     rewrite nth_put 1:/#.
     move: H32 H33 H34.
     have ->: to_uint ((offset{1} - (of_int 2)%W64) * (of_int 32)%W64) = (to_uint offset{1} - 2) * 32.
       * rewrite to_uintM of_uintK /=.
         rewrite to_uintB; first by rewrite uleE /#.
         rewrite of_uintK /#.
     move => H32 H33 H34.
     case (to_uint offset{1} - 2 = j %/ n) => H.
       * rewrite -H29 get_to_list -H33 /#. 
       * rewrite H32 1:/#.
         have ->: _stack{1}.[j] = nth witness (sub _stack{1} 0 (n * to_uint offset{1})) j by rewrite nth_sub /#.
         by rewrite H19 /sub_list nth_mkseq 1:/# /= nth_nbytes_flatten 1:/#.
   + rewrite Hcond /treehash_cond.
     have ->: to_uint (offset{1} - W64.one - W64.one) = to_uint offset{1} - 2 by rewrite to_uintB; [by rewrite uleE to_uintB 2:/# uleE /# | by rewrite /= to_uintB 2:/# uleE /#].
     have ->: to_uint (offset{1} - W64.one) = to_uint offset{1} - 1 by rewrite to_uintB 2:/# uleE /#.
     reflexivity.
   + have E21: (2 <= to_uint offset{1} /\heights{1}.[to_uint offset{1} - 2] = heights{1}.[to_uint offset{1} - 1]) by smt().
     move: E21 => [#] Ha Hb.
      admit. (* 2 <= to_uint offset{1} - 1 *)
   + rewrite !nth_put 1,2:/# ifT // ifF 1:/#. 
     move: Hcond. 
     have ->: to_uint (offset{1} - W64.one - W64.one) = to_uint offset{1} - 2 by rewrite to_uintB; [by rewrite uleE to_uintB 2:/# uleE /# | by rewrite /= to_uintB 2:/# uleE /#].
     rewrite /treehash_cond.
     have ->: to_uint (offset{1} - W64.one) = to_uint offset{1} - 1 by rewrite to_uintB 2:/# uleE /#.
     have E21: (2 <= to_uint offset{1} /\heights{1}.[to_uint offset{1} - 2] = heights{1}.[to_uint offset{1} - 1]) by smt().
     move: E21 => [Ha Hb].
     rewrite !get_setE 1,2:/# ifF 1:/# ifT 1:/# /=.
     move => Hcond.
     rewrite -E1 1:/#. 

     
     rewrite Hb. rewrite to_uintK.
     rewrite E1 1:/#.

     admit.
   + move => Ha.
     rewrite !nth_put 1,2:/# ifT // ifF 1:/#.
     rewrite -!E1 1,2:/# => Hb.
     rewrite Hcond /treehash_cond.
     do split; first by smt(@W64 pow2_64).
     have ->: to_uint (offset{1} - W64.one - W64.one) = to_uint offset{1} - 2 by rewrite to_uintB; [by rewrite uleE to_uintB 2:/# uleE /# | by rewrite /= to_uintB 2:/# uleE /#].
     have ->: to_uint (offset{1} - W64.one) = to_uint offset{1} - 1 by rewrite to_uintB 2:/# uleE /#.
     rewrite !get_setE 1,2:/# /= ifF 1:/#. 
     have ->: heights{1}.[to_uint offset{1} - 3] = W32.of_int (to_uint  heights{1}.[to_uint offset{1} - 3]) by rewrite to_uintK.
     have ->: heights{1}.[to_uint offset{1} - 2] + W32.one = W32.of_int (to_uint heights{1}.[to_uint offset{1} - 2] + 1) by smt(@W32 pow2_32).
     by rewrite !Hb.
qed.

*)
