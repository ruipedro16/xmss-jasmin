pragma Goals : printall.

require import AllCore List RealExp IntDiv Distr DList.
from Jasmin require import JModel JArray.

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

lemma eq_symm ['a] (a b : 'a) : a = b => b = a by move => ->.

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


unroll {1} 2; unroll {2} 2.
sp 1 1.
rcondt {1} 1.
      + auto => /> &hr ???????????????H.
        rewrite ultE H /=. 
        by apply pow2_pos.
rcondt {2} 1.
      + auto => &hr *.
        smt(pow2_pos).

seq 2 0 : (#pre /\ to_uint t32{1} = s{2} + i{2}); first by auto.

swap {1} 2 -1.

seq 1 2 : ( 
    #{/~sub ots_addr{1} 0 3 = sub address{2} 0 3}
     {/~address{2} = _addr}
     {/~address{2}.[4] = W32.zero}pre /\ 
     sub ots_addr{1} 0 5 = sub address{2} 0 5
).
 
    + inline {1}; auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16.  
      do split; (
         apply (eq_from_nth witness); [by rewrite !size_sub | rewrite size_sub // => j?];
         rewrite !nth_sub //= !get_setE //
      ).
         * do (rewrite ifF 1:/#).
           have ->: ltree_addr{1}.[j] = nth witness (sub ltree_addr{1} 0 3) j by rewrite nth_sub.
           by rewrite H10 nth_sub.
         * do (rewrite ifF 1:/#).
           have ->: node_addr{1}.[j] = nth witness (sub node_addr{1} 0 3) j by rewrite nth_sub.
           by rewrite H11 nth_sub.
         * case (j = 4) => ?.
              - smt(@W32 pow2_32).
              - do 3! (rewrite ifF 1:/#).
                case (j = 3) => [/# |?].
                have ->: ots_addr{1}.[j] = nth witness (sub ots_addr{1} 0 3) j by rewrite nth_sub /#.
                rewrite H9 nth_sub /#.

seq 1 0 : (#pre /\ ltree_addr{1}.[4] = W32.of_int (s{2} + i{2})).
    + inline {1}; auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16. 
      split.
         * apply (eq_from_nth witness); first by rewrite !size_sub.
           rewrite size_sub // => i?.
           rewrite !nth_sub // get_setE // ifF 1:/# /=.
           have ->: ltree_addr{1}.[i] = nth witness (sub ltree_addr{1} 0 3) i by rewrite nth_sub.
           by rewrite H9 nth_sub.
         * smt(@W32 pow2_32).

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
           auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 resultL resultR H18 H19.
           do split; [
               have ->: P6.[0] = nth witness (sub P6 0 5) 0 by rewrite nth_sub | 
               have ->: P6.[1] = nth witness (sub P6 0 5) 1 by rewrite nth_sub |     
               have ->: P6.[2] = nth witness (sub P6 0 5) 2 by rewrite nth_sub |
           ]; 1..3: by  rewrite -H17 -H19 nth_sub /#.        
           have ->: resultL.`2.[3] = nth witness (sub resultL.`2 0 5) 3 by rewrite nth_sub /#.
           by rewrite H19 nth_sub.

seq 0 2 : (
          #{/~sub ots_addr{1} 0 5 = sub address{2} 0 5}pre /\ 
          sub ltree_addr2{1} 0 5 = sub address{2} 0 5
      ).
         * auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20. 
           rewrite /set_ltree_addr /set_type.
           do split; (
              apply (eq_from_nth witness); [by rewrite !size_sub | rewrite size_sub // => i?];
              rewrite !nth_sub // !get_setE //=
           ).
               - do (rewrite ifF 1:/#).
                 have ->: ltree_addr{1}.[i] = nth witness (sub ltree_addr{1} 0 3) i by rewrite nth_sub.
                 by rewrite H9 nth_sub.
               - do (rewrite ifF 1:/#).
                 have ->: node_addr{1}.[i] = nth witness (sub node_addr{1} 0 3) i by rewrite nth_sub.
                 by rewrite H10 nth_sub.
               - case (i = 4) => [-> /# |?].
                 case (i = 3) => [-> /# |?].
                 do (rewrite ifF 1:/#).
                 have ->: ltree_addr{1}.[i] = nth witness (sub ltree_addr{1} 0 3) i by rewrite nth_sub /#.
                 by rewrite H9 nth_sub /#.

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

auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25.
      do split.
         * apply (eq_from_nth witness); first by rewrite !size_sub.
           rewrite size_sub // => i?. 
           rewrite !nth_sub /#.
         * by rewrite H21.
         * apply (eq_from_nth witness); first by rewrite !size_sub.
           rewrite size_sub // => i?. 
           rewrite !nth_sub /#.

(* ================================================== proof for gen leaf ends here =================================================================== *)

seq 3 1 : (
    #pre /\ 
    sub _stack{1} 0 (n * ((to_uint offset{2}) + 1)) =
    sub_list (nbytes_flatten stack{2}) 0 (n * ((to_uint offset{2}) + 1))
).
    + exists * buf{1}, stack{2}, _stack{1}, offset{1}.
      elim * => P0 P1 P2 P3. 
      sp.
      call {1} (p_treehash_memcpy P0 P1 P2 P3) => [/# |].
      skip => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17. 
      do split. 
        - smt().
        - apply (eq_from_nth witness); first by rewrite size_sub 1:/# size_sub_list /#.
          rewrite size_sub 1:/# /XMSS_N (: 32 * min 0 (size P1) = 0) 1:/# => j?.
          smt().
        - move => H24 H25 result H26.
          rewrite size_put; split => //. (* the first goal of split is solved by trivial *)
          apply (eq_from_nth witness); first by rewrite size_sub 1:/# size_sub_list /#.
          rewrite size_sub 1:/# => j?.
          rewrite n_val.
          rewrite /XMSS_N (: (32 * min 1 (size P1)) = 32) 1:/# in H26.
          rewrite H26.
          do congr.
          smt(@NBytes).
 
conseq />.

seq 1 1 : ( 
  #{/~sub _stack{1} 0 (n * (to_uint offset{2} + 1)) = sub_list (nbytes_flatten stack{2}) 0 (n * (to_uint offset{2} + 1))}
   {/~ offset{1} = W64.zero}pre /\
   offset{1} = W64.one /\
   sub _stack{1} 0 (n * to_uint offset{2}) = sub_list (nbytes_flatten stack{2}) 0 (n * to_uint offset{2})
); first by auto.

seq 1 1 : (#pre /\ sub heights{1} 0 1 = sub_list heights{2} 0 1).
    + auto => /> &1 &2 *.
      rewrite !size_put; do split => //.
      apply (eq_from_nth witness); first by rewrite size_sub // size_sub_list.
      rewrite size_sub // => j?.
      rewrite nth_sub // /sub_list nth_mkseq //=.
      rewrite get_setE //= nth_put //=/#.

seq 1 0 : (#pre /\ cond{1} = W8.zero).
    + ecall {1} (p_treehash_condition_if heights{1} offset{1}).
      auto => /> &1 &2 *.

rcondf {2} 2; first by auto.
rcondf {1} 1; first by auto => /> *; smt(@W8).

swap {2} 2 -1.
seq 1 1 : (
    #{/~i{2} = 0}{/~i{1} = W32.zero}{/~to_uint t32{1} = s{2} + i{2}}pre /\ 
    i{1} = W32.one /\ 
    i{2} = 1
); first by auto.

seq 0 1 : #pre.
    + auto => /> &1 &2 *.
      do split; (
      apply (eq_from_nth witness); [by rewrite !size_sub // | rewrite size_sub // => j?];
      rewrite !nth_sub //= !get_setE //;
      do rewrite ifF 1:/#; smt(sub_k)     
    ).

while (
      t{2} = to_uint target_height{1} /\ 0 <= t{2} <= h /\
      s{2} = to_uint start_index{1} /\ 0 <= s{2} <= h /\ 

      0 < to_uint offset{2} <= to_uint i{1} /\ 
      ={offset} /\  
      
      0 < i{2} <= 2^t{2} /\ to_uint i{1} = i{2} /\
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

(* ============= LAST SUBGOAL OF (the first) WHILE STARTS HERE ============= *)

+ auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 *.
  do split; 1,2: by smt().
        * apply pow2_leq_1. 
        * apply H0.
        * apply (eq_from_nth witness); first by rewrite size_sub 1:/# size_sub_list /#.
          rewrite size_sub /#.
        * apply (eq_from_nth witness); first by rewrite size_sub 1:/# size_sub_list /#.
          rewrite  size_sub /#.
        - rewrite ultE /#.
        - rewrite ultE /#.
        - move => stackL heightsL iL ltree_addrL node_addrL ots_addrL addressR heightsR offsetR stackR.      
          rewrite ultE => H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 *.
          apply (eq_from_nth witness); first by rewrite size_sub 1:/# valP n_val.
          rewrite size_sub 1:/# n_val => j?.
          have ?: 0 < to_uint iL by smt(pow2_neq_0).
          have := H33.
          rewrite /sub /sub_list/XMSS_TREE_HEIGHT /= n_val => T.
          rewrite nth_mkseq 1:/# /=.
          have ->: stackL.[j] = nth witness (mkseq (fun (i0 : int) => stackL.[i0]) (32 * min (to_uint offsetR) (size stackR))) j by rewrite nth_mkseq //; smt(@W64 pow2_64).
          rewrite T nth_mkseq /=; first by smt(@W64 pow2_64).
          rewrite nth_nbytes_flatten /#.

(* ============= LAST SUBGOAL OF (the first) WHILE ENDS HERE ============= *)

(* ============= FIRST SUBGOAL OF WHILE STARTS HERE ============= *)

seq 2 0 : (#pre /\ to_uint t32{1} = s{2} + i{2}).
    + auto => /> &1 &2; rewrite ultE => *.
      rewrite to_uintD_small //=. 
      smt(@IntDiv @RealExp).
 
swap {1} 2 -1.

seq 1 2 : (
    #{/~sub ots_addr{1} 0 3 = sub address{2} 0 3}pre /\ sub ots_addr{1} 0 5 = sub address{2} 0 5
).
    + inline {1}; auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 *. 
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
    + inline {1}; auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 *.
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
           auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 resL resR H25 H26*.
           do split; [
               have ->: P6.[0] = nth witness (sub P6 0 5) 0 by rewrite nth_sub | 
               have ->: P6.[1] = nth witness (sub P6 0 5) 1 by rewrite nth_sub |     
               have ->: P6.[2] = nth witness (sub P6 0 5) 2 by rewrite nth_sub |
           ]; 1..3: by rewrite -H22 -H26 nth_sub /#.        
           have ->: resL.`2.[3] = nth witness (sub resL.`2 0 5) 3 by rewrite nth_sub /#.
           by rewrite H26 nth_sub.


seq 0 2 : (
          #{/~sub ots_addr{1} 0 5 = sub address{2} 0 5}pre /\ 
          sub ltree_addr2{1} 0 5 = sub address{2} 0 5
      ).
         * auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26*.
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

auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 *.
      do split.
         * apply (eq_from_nth witness); first by rewrite !size_sub.
           rewrite size_sub // => i?. 
           rewrite !nth_sub /#.
         * by rewrite H28.
         * apply (eq_from_nth witness); first by rewrite !size_sub.
           rewrite size_sub // => i?. 
           rewrite !nth_sub /#.

(* ================================================== proof for gen leaf ends here =================================================================== *)
 
seq 3 1 : (
        #{/~sub _stack{1} 0 (n * min (to_uint offset{2}) (size stack{2})) = sub_list (nbytes_flatten stack{2}) 0 (n * min (to_uint offset{2}) (size stack{2}))}pre /\
          sub _stack{1} 0 (n * min (to_uint offset{2} + 1) (size stack{2})) =
          sub_list (nbytes_flatten stack{2}) 0 (n * min (to_uint offset{2} + 1) (size stack{2}))
).
    + exists * buf{1}, stack{2}, _stack{1}, offset{1}.
      elim * => P0 P1 P2 P3. 
      sp.
      call {1} (p_treehash_memcpy P0 P1 P2 P3) => [/# |].
      skip => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 *.
      do split. 
        - smt().
        - smt(). 
        - smt(). 
        - move => H24 H25 H26 result H27 *.
          rewrite size_put; split => //. (* the first goal of split is solved by trivial *)
          apply (eq_from_nth witness); first by rewrite size_sub 1:/# size_sub_list /#.
          rewrite size_sub 1:/# => j?.
          rewrite n_val.
          rewrite /XMSS_N in H27.
          case (0 <= to_uint offset{2} < size P1) => ?.
          (* === in bounds case === *)
          have E: min (to_uint offset{2} + 1) (size P1) = to_uint offset{2} + 1 by smt().
          rewrite H27 E.
          do congr.
          smt(@NBytes).
          (* === out of bounds case === *)
          rewrite put_out; first by smt(@W64 pow2_64).
          have E: min (to_uint offset{2} + 1) (size P1) = size P1 by smt().
          rewrite H27 E H25.
          do congr.
          rewrite put_out // /#.

conseq />.
 
seq 1 1 : (
  #{/~sub heights{1} 0 (min (to_uint offset{2}) (size heights{2})) = sub_list heights{2} 0 (min (to_uint offset{2}) (size heights{2}))}
   {/~sub _stack{1} 0 (n * min (to_uint offset{2} + 1) (size stack{2})) =
          sub_list (nbytes_flatten stack{2}) 0 (n * min (to_uint offset{2} + 1) (size stack{2}))}
   {/~to_uint offset{2} <= to_uint i{1}}pre /\

   sub _stack{1} 0 (n * min (to_uint offset{2}) (size stack{2})) = sub_list (nbytes_flatten stack{2}) 0 (n * min (to_uint offset{2}) (size stack{2})) /\
   sub heights{1} 0 (min (to_uint (offset{2} - W64.one)) (size heights{2})) = sub_list heights{2} 0 (min (to_uint (offset{2} - W64.one)) (size heights{2})) /\
   to_uint (offset{2} - W64.one) <= to_uint i{1}
).
    + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 *. 
      have E3: 0 <= to_uint i{1} <= 2 ^ 20 by smt(@RealExp).
      do split. 
      - rewrite to_uintD /= /#. (* This call to smt doesnt work without E1 in the context *)
      - apply (eq_from_nth witness).
          * rewrite size_sub; first by smt(@W64 pow2_64).
            by rewrite size_sub_list; first by smt(@W64 pow2_64).
        rewrite size_sub; first by smt(@W64 pow2_64).
        case (0 <= to_uint (offset{2} + W64.one) < size stack{2}) => ?.
          * have E1: min (to_uint (offset{2} + W64.one)) (size stack{2}) = to_uint (offset{2} + W64.one) by smt().
            have E2: 0 <= to_uint (offset{2} + W64.one) < 11 by smt().
            rewrite E1 n_val => j?.
            rewrite nth_sub //= /sub_list nth_mkseq //= nth_nbytes_flatten; first by smt(@W64 pow2_64).
            have ->: _stack{1}.[j] = nth witness (sub _stack{1} 0 (n * min (to_uint offset{2} + 1) (size stack{2}))) j by rewrite nth_sub; first by smt(@W64 pow2_64).
            rewrite H23 /sub_list nth_mkseq; first by smt(@W64 pow2_64).
            rewrite /= nth_nbytes_flatten // /#.
          * have E1: min (to_uint (offset{2} + W64.one)) (size stack{2}) = size stack{2} by smt(@W64 pow2_64).
            rewrite E1 H9 d_val h_val n_val /= => j?. 
            rewrite nth_sub //.
            rewrite /sub_list nth_mkseq //= nth_nbytes_flatten 1:/#.
            have ->: _stack{1}.[j] = nth witness (sub _stack{1} 0 (n * min (to_uint offset{2} + 1) (size stack{2}))) j by rewrite nth_sub; first by smt(@W64 pow2_64).
            rewrite H23 /sub_list nth_mkseq; first by smt(@W64 pow2_64).
            rewrite /= nth_nbytes_flatten // /#.
      - apply (eq_from_nth witness).  
          * rewrite size_sub; first by smt(@W64 pow2_64). 
            by rewrite size_sub_list; first by smt(@W64 pow2_64).
        rewrite size_sub; first by smt(@W64 pow2_64).
        have ->: to_uint (offset{2} + W64.one - W64.one) = to_uint offset{2} by smt(@W64 pow2_64).
        smt().
      - have ->: to_uint (offset{2} + W64.one - W64.one) = to_uint offset{2} by smt(@W64 pow2_64).
        apply H5.

seq 1 1 : (
  #{/~sub heights{1} 0 (min (to_uint (offset{2} - W64.one)) (size heights{2})) = sub_list heights{2} 0 (min (to_uint (offset{2} - W64.one)) (size heights{2}))}pre /\
  sub heights{1} 0 (min (to_uint offset{2}) (size heights{2})) = sub_list heights{2} 0 (min (to_uint offset{2}) (size heights{2}))
).
    + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23.
      rewrite size_put; split => //.
      apply (eq_from_nth witness).
         - rewrite size_sub; first by smt(@W64 pow2_64).
           by rewrite size_sub_list; first by smt(@W64 pow2_64).
      rewrite size_sub; first by smt(@W64 pow2_64).
      case (0 <= to_uint offset{2} <= size heights{2}) => ?.
         - have E1 : min (to_uint offset{2}) (size heights{2}) = to_uint offset{2} by smt().
           rewrite E1 => j?.
           rewrite nth_sub //= /sub_list nth_mkseq //= nth_put; first by smt(@W64 pow2_64).
           rewrite get_setE; first by smt(@W64 pow2_64).
           case (j = to_uint (offset{2} - W64.one)) => [/# | ? //=].
           rewrite ifF 1:/#.
           have ->: heights{1}.[j] = nth witness (sub heights{1} 0 (min (to_uint (offset{2} - W64.one)) (size heights{2}))) j by rewrite nth_sub; smt(@W64 pow2_64).
           rewrite H22 /sub_list nth_mkseq; first by smt(@W64 pow2_64).
           trivial.
         - have E1 : min (to_uint offset{2}) (size heights{2}) = size heights{2} by smt().
           rewrite E1 H9 h_val d_val /= => j?.
           rewrite nth_sub // /sub_list nth_mkseq //=.
           rewrite put_out; first by smt(@W64 pow2_64).
           rewrite get_set_if.
           rewrite ifF; first by smt(@W64 pow2_64).
           have ->: heights{1}.[j] = nth witness (sub heights{1} 0 (min (to_uint (offset{2} - W64.one)) (size heights{2}))) j by rewrite nth_sub; smt(@W64 pow2_64).
           rewrite H22 /sub_list nth_mkseq; first by smt(@W64 pow2_64).
           trivial.

conseq />.   

seq 1 0 : (
    #pre /\ 
    (cond{1} = W8.one) = 
    (W64.of_int 2 \ule offset{2} /\ heights{1}.[to_uint (offset{1} - W64.of_int 2)] = heights{1}.[to_uint (offset{1} - W64.one)])
); first by  ecall {1} (p_treehash_condition_correct_eq heights{1} offset{1}); auto.

seq 0 1 : (#{/~sub node_addr{1} 0 3 = sub address{2} 0 3}pre /\ sub node_addr{1} 0 5 = sub address{2} 0 5).
  + auto => /> &1 &2 *.
    rewrite /set_type.
    do split; (
      apply (eq_from_nth witness); [by rewrite !size_sub // | rewrite size_sub // => j?];
      rewrite !nth_sub //= !get_setE //     
    ).
      - do rewrite ifF 1:/#; smt(sub_k).
      - do rewrite ifF 1:/#; smt(sub_k).
      - do 3! (rewrite ifF 1:/#).
        case (j = 3) => [-> /# |?].
        case (j = 4) => [-> /# |?].
        smt(sub_k).

while (
  t{2} = to_uint target_height{1} /\
  0 <= t{2} <= h /\

  s{2} = to_uint start_index{1} /\
  0 <= s{2} <= h /\

  ={offset} /\
  (0 < to_uint offset{2})/\
    to_uint (offset{2} - W64.one) <= to_uint i{1} /\
  0 < i{2} <= 2 ^ t{2} /\
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
); last first.

(* === the last subgoal of the second while starts here === *)

auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 *.
have E: forall (k : int), 0 <= k < (min (to_uint offset{2}) (size heights{2})) => heights{1}.[k] = nth witness heights{2} k.
        * move => k?.
          have ->: heights{1}.[k] = nth witness (sub heights{1} 0 (min (to_uint offset{2}) (size heights{2}))) k by rewrite nth_sub; smt(@W64 pow2_64).
          by rewrite H22 /sub_list nth_mkseq.

do split. 
    - smt(@W64 pow2_64).
    - rewrite H23.
      move => [#] Ha Hb.
      split; first by assumption.
      case (0 <= to_uint offset{2} < size heights{2}) => ?. (* offset - 2 e offset - 1 estao in bounds pq offset < size heights*)
        + have E1: min (to_uint offset{2}) (size heights{2}) = to_uint offset{2} by smt().
          rewrite -!E; 1,2: by rewrite E1; smt(@W64 pow2_64).
          by rewrite Hb.
        + have E1: min (to_uint offset{2}) (size heights{2}) = size heights{2} by smt().
        (* Neste caso, offset >= size heights, mas offset - 1 e offset - 2 podem estar in bounds *)
          case (0 <= to_uint (offset{2} - W64.one) < (size heights{2})) => Hc1.
            * (* Neste caso, offset - 1 e offset - 2 estao in bounds *)
              rewrite -!E; 1,2: by smt(@W64 pow2_64).
              by rewrite Hb.
            * (* Neste caso, offset - 1 esta out of bounds, mas offset - 2 ainda pode estar in bounds *)
              case (0 <= to_uint (offset{2} - (of_int 2)%W64) < (size heights{2})) => ?. (* offset - 2 esta in bounds mas offset - 1 esta out of bounds *)
                 - rewrite nth_out //.
                   rewrite -E; first by rewrite E1. 
                   rewrite eq_sym in Hb.
                   rewrite -Hb. 
                   rewrite get_out //. 
                   rewrite (: size heights{2} = 11) 1:/# in Hc1.
                   apply Hc1.
              (* Por fim, esta tudo out of bounds *)
              by rewrite !nth_out.
    - rewrite H23.
      move => [#] Ha Hb.
      split; first by assumption.
      case (0 <= to_uint offset{2} < size heights{2}) => ?. (* offset - 2 e offset - 1 estao in bounds pq offset < size heights*)
        + have E1: min (to_uint offset{2}) (size heights{2}) = to_uint offset{2} by smt().
          rewrite !E; 1,2: by rewrite E1; smt(@W64 pow2_64).
          by rewrite Hb.
        + have E1: min (to_uint offset{2}) (size heights{2}) = size heights{2} by smt().
        (* Neste caso, offset >= size heights, mas offset - 1 e offset - 2 podem estar in bounds *)
          case (0 <= to_uint (offset{2} - W64.one) < (size heights{2})) => Hc1; rewrite (: size heights{2} = 11) 1:/# in Hc1.
            * (* Neste caso, offset - 1 e offset - 2 estao in bounds *)
              rewrite !E; 1,2: by smt(@W64 pow2_64).
              by rewrite Hb.
            * (* Neste caso, offset - 1 esta out of bounds, mas offset - 2 ainda pode estar in bounds *)
              case (0 <= to_uint (offset{2} - (of_int 2)%W64) < (size heights{2})) => ?. (* offset - 2 esta in bounds mas offset - 1 esta out of bounds *)
                 - rewrite eq_sym get_out //. 
                   rewrite E; first by rewrite E1. 
                   rewrite eq_sym in Hb.
                   rewrite Hb. 
                   rewrite nth_out //.
                   rewrite (: size heights{2} = 11) 1:/# ; apply Hc1.
              (* Por fim, esta tudo out of bounds *)
              rewrite !get_out // /#.
                
    - move => stackL condL heightsL nodeAdrL addressR heightsR offsetR stackR.
      move => H25 H26 H27 H28 H29 H30 H31 H32 H33 HH35 H36 H37 H38 H39 *.
      have E3: 0 <= to_uint i{1} <= 2 ^ 20 by smt(@RealExp). (* Same as before *)
      do split.
        * rewrite to_uintD_small 1:/#.
          have := H28.
          rewrite to_uintB; [by rewrite uleE /# => T |].
          smt(). (* Este smt so funciona depois de simplificarmos um bocado a hipotese H28 *)
        * smt().
        * smt().
        * smt(@W32 pow2_32).
        * smt(sub_N).
        * smt(@W32 pow2_32).
        * smt(@W32 pow2_32).

(* === the last subgoal of the second while ends here === *)

seq 2 0 : (#pre /\ tree_idx{1} = (of_int (s{2} + i{2}))%W32).
    + auto => /> &1 &2 *; smt(@W32 pow2_32).

seq 2 0 : (#pre /\ u{1} = (nth witness heights{2} (to_uint (offset{2} - W64.one)) + W32.one)).
    + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 *.  
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
            rewrite H18. 
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
      auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 *.
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
            rewrite H18. 
            rewrite -E2 E1 /sub_list nth_mkseq 2:/#.
            smt(@W64 pow2_64).
          - (* In this case (min offset (size heights)) = size heights *)
            have E1 : min (to_uint offset{2}) (size stack{2}) = size stack{2} by smt().
            have E2 : size stack{2} = size heights{2} by smt().
            rewrite nth_out; first by smt(@W64 pow2_64).
            rewrite get_out; first by smt(@W64 pow2_64).
            reflexivity.


seq 4 2 : (#pre /\ to_list buf2{1} = val node0{2} ++ val node1{2}).
    + sp.
      exists * _stack{1}, offset{1}, stack{2}.
      elim * => P0 P1 P2.
      call {1} (memcpy_treehash_node_2 P0 P1 P2) => [/# |].
      skip => /> &1 &2 /#.

seq 1 1 : (#pre /\ to_list buf{1} = val new_node{2}).
          + inline M(Syscall).__thash_h_ M(Syscall)._thash_h.
            wp; sp.
            exists * node0{2}, node1{2}, pub_seed1{1}, addr0{1}, address{2}.
            elim * => P0 P1 P2 P3 P4.
            call (rand_hash_results P0 P1 P2 P3 P4) => [/# |].
            auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 *.
            do split. 
                 - rewrite /merge_nbytes_to_array tP => i?.
                   rewrite  -get_to_list H26 initiE // nth_cat valP n_val.
                   case (0 <= i < 32) => ?; [by rewrite ifT 1:/# ifT 1:/# | by  rewrite ifF 1:/# ifF 1:/#].
                 - smt(sub_k).           
                 - move => ?? resL resR ? H.
                   do split; [| smt() | smt() |]; (
                            apply (eq_from_nth witness); [by rewrite !size_sub | rewrite size_sub // => j?]
                   ); [rewrite -H12 | rewrite -H25]; rewrite !nth_sub //=/#.

ecall {1} (p_treehash_condition_correct_eq heights{1} offset{1}).
 
conseq /> => [/# |].
 
seq 3 0 : (#pre /\ t64{1} = (offset{1} - (of_int 2)%W64) * (of_int 32)%W64); first by auto.

seq 1 1 : #pre.
    + exists * buf{1}, stack{2}, _stack{1}, offset{2}.
      elim * => P0 P1 P2 P3.  
      call {1} (p_treehash_memcpy_2 P0 P1 P2 P3) => [/# |].
      auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 *.
      rewrite !size_put.
      do split.
        - smt(@W64 pow2_64).
        - smt(). 
        - move => H27 H28 result ->.
          split => //.
          do congr.
          smt(@NBytes).
 
auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 cond ->.
rewrite !size_put /treehash_cond.
do split => //.
    + smt(@W64 pow2_64).
    + smt(@W64 pow2_64).
    + apply (eq_from_nth witness).
        * rewrite size_sub; first by smt(@W64 pow2_64).
          rewrite size_sub_list; smt(@W64 pow2_64).
      rewrite size_sub; first by smt(@W64 pow2_64).
      move => j Hj.
      have ->: to_uint (offset{2} - W64.one - W64.one) = to_uint (offset{2} - (of_int 2)%W64) by smt(@W64 pow2_64).

      have E: forall (k : int), 0 <= k < (min (to_uint offset{2}) (size heights{2})) => heights{1}.[k] = nth witness heights{2} k.
        * move => k?.
          have ->: heights{1}.[k] = nth witness (sub heights{1} 0 (min (to_uint offset{2}) (size heights{2}))) k by rewrite nth_sub; smt(@W64 pow2_64).
          by rewrite H18 /sub_list nth_mkseq.


      case (0 <= to_uint (offset{2} - (of_int 2)%W64) < size heights{2}) => Ha; last first.
        * rewrite put_out; first by smt(@W64 pow2_64).
          rewrite nth_sub // get_set_if ifF /=; first by smt(@W64 pow2_64).
          rewrite /sub_list nth_mkseq //=.
          have ->: nth witness heights{2} j = nth witness (sub_list heights{2} 0 (min (to_uint offset{2}) (size heights{2}))) j 
                   by rewrite /sub_list nth_mkseq //=; smt(@W64 pow2_64).
          rewrite -H18 nth_sub; smt(@W64 pow2_64).
        * rewrite nth_sub // get_setE; first by smt(@W64 pow2_64).
          rewrite /sub_list nth_mkseq //= nth_put; first by smt(@W64 pow2_64).
          case (j = to_uint (offset{2} - (of_int 2)%W64)) => H; [rewrite ifT 1:/# | rewrite ifF 1:/#]. 
             - rewrite E //; smt(@W64 pow2_64).
             - have ->: nth witness heights{2} j = nth witness (sub_list heights{2} 0 (min (to_uint offset{2}) (size heights{2}))) j
                        by  rewrite /sub_list nth_mkseq //; smt(@W64 pow2_64).
               by rewrite -H18 nth_sub //; smt(@W64 pow2_64).         
  
    + apply (eq_from_nth witness).
        * rewrite size_sub; first by smt(@W64 pow2_64).
          rewrite size_sub_list; smt(@W64 pow2_64).
      rewrite size_sub; first by smt(@W64 pow2_64).
      move => j Hj.
      have ->: nth witness (sub _stack{1} 0 (n * min (to_uint (offset{2} - W64.one)) (size stack{2}))) j = 
               nth witness (sub _stack{1} 0 (n * min (to_uint offset{2}) (size stack{2}))) j by rewrite !nth_sub; smt(@W64 pow2_64).
      rewrite H19.
      rewrite /sub_list !nth_mkseq; smt(@W64 pow2_64).

    + smt(@W64 pow2_64).

    + move => [#] Ha Hb.
      split; first by assumption.
      move: Hb.
      have E: forall (k : int), 0 <= k < (min (to_uint offset{2}) (size heights{2})) => heights{1}.[k] = nth witness heights{2} k.
        * move => k?.
          have ->: heights{1}.[k] = nth witness (sub heights{1} 0 (min (to_uint offset{2}) (size heights{2}))) k by rewrite nth_sub; smt(@W64 pow2_64).
          by rewrite H18 /sub_list nth_mkseq.
      have ->: offset{2} - W64.one - W64.one = offset{2} - (of_int 2)%W64 by smt(@W64 pow2_64).

      case (0 <= to_uint offset{2} < size heights{2}) => ?.
          (* Neste caso, offset - 2 e offset - 1 estao in bounds pq offset < size heights*)
        + have E1: min (to_uint offset{2}) (size heights{2}) = to_uint offset{2} by smt(). 
          rewrite !nth_put; 1,2: by smt(@W64 pow2_64).
          rewrite ifT // ifF; first by smt(@W64 pow2_64).
          rewrite !get_setE; 1,2: by smt(@W64 pow2_64).
          rewrite ifF; first by smt(@W64 pow2_64).
          rewrite ifT //.
          move => Hb.
          rewrite -!E; smt(@W64 pow2_64).

        + have E1: min (to_uint offset{2}) (size heights{2}) = size heights{2} by smt().
          case (0 <= to_uint (offset{2} - W64.one) < (size heights{2})) => ?.
              (* Neste caso, offset esta out of bounds, mas offset-1 e offset-2 estao in bounds *)
              * rewrite !E; first by rewrite E1; smt(@W64 pow2_64).
                rewrite !nth_put; 1,2: by smt(@W64 pow2_64).
                rewrite ifT // ifF; first by smt(@W64 pow2_64).
                rewrite !get_setE; 1,2: by smt(@W64 pow2_64).
                rewrite ifF; first by smt(@W64 pow2_64).
                rewrite ifT //.
                rewrite E; first by smt(@W64 pow2_64).
                by move => ->.
              * case (0 <= to_uint (offset{2} - (of_int 2)%W64) < (size heights{2})) => Hc1. 
                      (* offset - 2 esta in bounds mas offset - 1 esta out of bounds *)
                    - rewrite (: size heights{2} = 11) 1:/# in Hc1.
                      rewrite !nth_put; 1,2: by smt(@W64 pow2_64).
                      rewrite ifT // ifF; first by smt(@W64 pow2_64).
                      rewrite !get_setE; 1,2: by smt(@W64 pow2_64).
                      rewrite ifF; first by smt(@W64 pow2_64).
                      rewrite ifT //.
                      rewrite !E; 1,2: by smt(@W64 pow2_64).
                      by move => ->.
                    - rewrite get_set_if ifF; first by smt(@W64 pow2_64).
                      rewrite get_set_if ifF; first by smt(@W64 pow2_64).
                      rewrite put_out; first by smt(@W64 pow2_64).
                      case (0 <= to_uint (offset{2} - W64.one - (of_int 2)%W64) < (size heights{2})) => Hc2. 
                        + (* neste casso offset-3 ainda esta in bounds *) 
                          rewrite E; first by smt(@W64 pow2_64).
                          rewrite get_out; first by smt(@W64 pow2_64).
                          move => ->.
                          rewrite nth_out; first by smt(@W64 pow2_64).
                          reflexivity.
                        + by move => ?; rewrite !nth_out.
                          (* neste caso ja esta tudo out of bounds *)

    + move => [#] Ha Hb.
      split; first by assumption.
      move: Hb.
      have E: forall (k : int), 0 <= k < (min (to_uint offset{2}) (size heights{2})) => heights{1}.[k] = nth witness heights{2} k.
        * move => k?.
          have ->: heights{1}.[k] = nth witness (sub heights{1} 0 (min (to_uint offset{2}) (size heights{2}))) k by rewrite nth_sub; smt(@W64 pow2_64).
          by rewrite H18 /sub_list nth_mkseq.

      have ->: offset{2} - W64.one - W64.one = offset{2} - (of_int 2)%W64 by smt(@W64 pow2_64).
      case (0 <= to_uint offset{2} < size heights{2}) => ?. 
          (* Neste caso, offset - 2 e offset - 1 estao in bounds pq offset < size heights*)
        + have E1: min (to_uint offset{2}) (size heights{2}) = to_uint offset{2} by smt(). 
          rewrite !E; first by rewrite E1; smt(@W64 pow2_64).
          rewrite !nth_put; 1,2: by smt(@W64 pow2_64).
          rewrite ifT //.
          rewrite ifF; first by smt(@W64 pow2_64).
          move => Hb.
          rewrite !get_setE; 1,2: by smt(@W64 pow2_64).
          rewrite ifF; first by smt(@W64 pow2_64).
          rewrite ifT //.
          rewrite E; first by smt(@W64 pow2_64).
          by rewrite Hb.

        + have E1: min (to_uint offset{2}) (size heights{2}) = size heights{2} by smt().
          case (0 <= to_uint (offset{2} - W64.one) < (size heights{2})) => ?.
              (* Neste caso, offset esta out of bounds, mas offset-1 e offset-2 estao in bounds *)
              * rewrite !E; first by rewrite E1; smt(@W64 pow2_64).
                rewrite nth_put; first by smt(@W64 pow2_64).
                rewrite ifT //.
                rewrite nth_put; first by smt(@W64 pow2_64).
                rewrite ifF; first by smt(@W64 pow2_64).
                move => Hb.
                rewrite !get_setE; 1,2: by smt(@W64 pow2_64).
                rewrite ifF; first by smt(@W64 pow2_64).
                rewrite ifT //.
                rewrite E; first by smt(@W64 pow2_64).
                by rewrite Hb.
              * case (0 <= to_uint (offset{2} - (of_int 2)%W64) < (size heights{2})) => Hc1. 
                      (* offset - 2 esta in bounds mas offset - 1 esta out of bounds *)
                    - rewrite (: size heights{2} = 11) 1:/# in Hc1.
                      rewrite !E; first by rewrite E1; smt(@W64 pow2_64).
                      rewrite !nth_put; 1,2: by smt(@W64 pow2_64).
                      rewrite ifT // ifF; first by smt(@W64 pow2_64).
                      move => Hb.
                      rewrite !get_setE; 1,2: by smt(@W64 pow2_64).
                      rewrite ifF; first by smt(@W64 pow2_64).
                      rewrite ifT //.
                      rewrite Hb.
                      by rewrite E //; smt(@W64 pow2_64).
                    - case (0 <= to_uint (offset{2} - W64.one - (of_int 2)%W64) < (size heights{2})) => Hc2. 
                        + (* neste casso offset-3 ainda esta in bounds *) 
                          rewrite put_out; first by smt(@W64 pow2_64).
                          rewrite nth_out; first by smt(@W64 pow2_64).
                          move => Hb. 
                          rewrite get_set_if ifF; first by smt(@W64 pow2_64).
                          rewrite get_set_if ifF; first by smt(@W64 pow2_64).
                          have ->: heights{1}.[to_uint (offset{2} - (of_int 2)%W64)] = witness
                                   by rewrite get_out; first by smt(@W64 pow2_64).
                          rewrite Hb E //.
                          smt(@W64 pow2_64).

                        + move => ?.
                          rewrite get_set_if ifF; first by smt(@W64 pow2_64).
                          rewrite get_set_if ifF; first by smt(@W64 pow2_64).  
                          rewrite get_out; first by smt(@W64 pow2_64).  
                          rewrite get_out; first by smt(@W64 pow2_64).  
                          reflexivity.                  
                          (* neste caso ja esta tudo out of bounds *)

qed.
