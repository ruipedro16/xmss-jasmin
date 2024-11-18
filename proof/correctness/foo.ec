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
require import Correctness_Conditions.
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

      0 <= to_uint _t <= h /\
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
  offset{2} = to_uint offset{1} /\
  ots_addr{1} = subtree_addr{1} /\
  ltree_addr{1} = subtree_addr{1} /\
  node_addr{1} = subtree_addr{1} /\
  node_addr{1}.[4] = W32.zero /\
  address{2}.[4] = W32.zero /\

  size stack{2} = h %/ d + 1 /\ (* = 21 *)
  size heights{2} = h %/ d      (* = 20 *)
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

seq 4 0 : (
  #{/~ots_addr{1} = subtree_addr{1}}
   {/~ltree_addr{1} = subtree_addr{1}}
   {/~node_addr{1} = subtree_addr{1}}pre /\
   sub ots_addr{1} 0 3 = sub address{2} 0 3 /\    (* coincidem nos indices 0, 1 e 2 *)
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
      t{2} = to_uint target_height{1} /\ 0 <= t{2} <= h /\ (* Target height *)
      s{2} = to_uint start_index{1} /\ 0 <= s{2} <= h /\ (* start index  *) 

      0 <= offset{2} < size heights{2} /\ offset{2} = to_uint offset{1} /\  
      (i{2} <> 0 => 0 < offset{2}) /\

      0 <= i{2} <= 2^t{2} /\ to_uint i{1} = i{2} /\
      to_uint upper_bound{1} = 2 ^ t{2} /\

      size stack{2} = h %/ d + 1 /\ 
      size heights{2} = h %/ d /\

      sk_seed{2} = (insubd (to_list sk_seed{1}))%NBytes /\
      pub_seed{2} = (insubd (to_list pub_seed{1}))%NBytes /\ 
      
      sub ots_addr{1} 0 3 = sub address{2} 0 3 /\
      sub ltree_addr{1} 0 3 = sub address{2} 0 3 /\
      sub node_addr{1} 0 3 = sub address{2} 0 3 /\

      ots_addr{1}.[3] = W32.zero /\       (* type *)
      ltree_addr{1}.[3] = W32.one /\      (* type *)
      node_addr{1}.[3] = W32.of_int 2 /\  (* type *)
      node_addr{1}.[4] = W32.zero /\      (* padding *)
      
      map W32.to_uint (sub heights{1} 0 offset{2}) = sub_list heights{2} 0 offset{2} /\
      (forall (k : int), 0 <= k < offset{2} => 0 <= nth witness heights{2} k < XMSS_FULL_HEIGHT) /\ 

      sub _stack{1} 0 (n * offset{2}) = sub_list (nbytes_flatten stack{2}) 0 (n * offset{2})
); last first.
    + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14.
      do split; 1,2,5: by smt().
        - smt(pow2_nonnegative).
        - apply (eq_from_nth witness); first by rewrite size_map size_sub // size_sub_list.
          rewrite size_map size_sub /#.
        - apply (eq_from_nth witness); first by rewrite size_sub // size_sub_list.
          rewrite size_sub /#.
        - rewrite ultE /#.
        - rewrite ultE /#.
        - move => _stack_L heights_L i_L ltree_addr_L node_add_L offset_L ots_addr_L address_R heights_R stack_R.
          rewrite ultE => H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34.
          apply (eq_from_nth witness); first by rewrite size_sub 1:/# valP n_val.
          rewrite size_sub 1:/# n_val => j?.
          have ?: 0 < to_uint i_L by smt(pow2_neq_0).
          have := H34.
          rewrite /sub /sub_list n_val.
          have ->: 32 * to_uint offset_L = 32 + 32 * (to_uint offset_L - 1) by smt().
          rewrite !(mkseq_add _ 32) 1..4:/# => H.
          have ->: mkseq (fun (i0 : int) => _stack_L.[0 + i0]) 32 = mkseq (fun (i0 : int) => nth witness (nbytes_flatten stack_R) (0 + i0)) 32.
             * have := eqseq_cat (mkseq (fun (i0 : int) => _stack_L.[0 + i0]) 32)
               (mkseq (fun (i0 : int) => nth witness (nbytes_flatten stack_R) (0 + i0)) 32) (* 1st argument *)
               (mkseq (fun (i0 : int) => (fun (i1 : int) => _stack_L.[0 + i1]) (32 + i0)) (32 * (to_uint offset_L - 1))) (* 2nd argument *)
               (mkseq (fun (i0 : int) => (fun (i1 : int) => nth witness (nbytes_flatten stack_R) (0 + i1)) (32 + i0)) (32 * (to_uint offset_L - 1))) (* 3rd argument *).
               by rewrite !size_mkseq /max //= H //=. 
          rewrite nth_mkseq //= /nbytes_flatten (nth_flatten witness n); last by rewrite (nth_map witness) /#.
          pose P := (fun (s0 : W8.t list) => size s0 = n).
              pose L := (map NBytes.val stack_R).
              rewrite -(all_nthP P L witness) /P /L size_map H23 d_val h_val /= => k?. 
              by rewrite (nth_map witness) 1:/# valP. 

seq 2 0 : (#pre /\ to_uint t32{1} = s{2} + i{2}).
    + auto => /> &1 &2 *.
      rewrite to_uintD_small //=. 
      smt(@IntDiv @RealExp). (* Este smt falha as vezes *)

swap {1} 2 -1.

seq 1 2 : (
    #{/~sub ots_addr{1} 0 3 = sub address{2} 0 3}pre /\ sub ots_addr{1} 0 5 = sub address{2} 0 5
).
    + inline {1}; auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24. 
      rewrite /set_ots_addr /set_type.
      do split; (
         apply (eq_from_nth witness); [by rewrite !size_sub | rewrite size_sub // => j?];
         rewrite !nth_sub //= !get_setE //
      ).
         * do (rewrite ifF 1:/#).
           have ->: ltree_addr{1}.[j] = nth witness (sub ltree_addr{1} 0 3) j by rewrite nth_sub.
           by rewrite H13 nth_sub.
         * do (rewrite ifF 1:/#).
           have ->: node_addr{1}.[j] = nth witness (sub node_addr{1} 0 3) j by rewrite nth_sub.
           by rewrite H14 nth_sub.
         * case (j = 4) => ?.
              - smt(@W32 pow2_32).
              - do 3! (rewrite ifF 1:/#).
                case (j = 3) => [/# |?].
                have ->: ots_addr{1}.[j] = nth witness (sub ots_addr{1} 0 3) j by rewrite nth_sub /#.
                rewrite H12 nth_sub /#.

wp.

seq 1 0 : (#pre /\ ltree_addr{1}.[4] = W32.of_int (s{2} + i{2})).
    + inline {1}; auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 *.
      split.
         * apply (eq_from_nth witness); first by rewrite !size_sub.
           rewrite size_sub // => i?.
           rewrite !nth_sub // get_setE // ifF 1:/# /=.
           have ->: ltree_addr{1}.[i] = nth witness (sub ltree_addr{1} 0 3) i by rewrite nth_sub.
           by rewrite H12 nth_sub.
         * by rewrite -H23 to_uintK.

seq 1 4 : (
  #{/~sub ots_addr{1} 0 5 = sub address{2} 0 5}
   {/~ltree_addr{1}.[4] = (of_int (s{2} + i{2}))%W32}pre /\
   val node{2} = to_list buf{1} /\ 
   sub ots_addr{1} 0 3 = sub address{2} 0 3
); first by admit.


seq 2 0 : (#pre /\ to_uint t64{1} = offset{2} * 32); first by auto => /> *; rewrite to_uintM of_uintK /=/#.
  
(* Neste ponto o invariante na parte do offset deixa de se verificar, mas ja se volta a verificar mais a frente *) 
seq 3 3 : (
   #{/~to_uint t64{1} = offset{2} * 32}{/~offset{2} < size heights{2}}pre /\
   0 <= offset{2} + 1 < size heights{2}   
).
    + wp. 
      exists * _stack{1}, buf{1}, t64{1}; elim * => P3 P4 P5.
      call {1} (memcpy_u8u8_3_352_32_post P3 P4 P5).
      auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 *.
      rewrite ultE in H21.
      do split; 1,2: by smt().
      rewrite H26 => H27 H28 result H29 H30 H31.
      do split. 
         - smt().
         - rewrite to_uintD /#.
         - smt().
         - rewrite size_put /#.
         - rewrite size_put /#.
         - apply (eq_from_nth witness); first by rewrite size_map size_sub 1:/# size_sub_list ///#.
           rewrite size_map size_sub 1:/# => j?.
           rewrite /sub_list nth_mkseq //= nth_put 1:/#. (* simplify rhs *)
           rewrite (nth_map witness); first by rewrite size_sub /#.
           rewrite nth_sub // get_setE // to_uintB /=; 1,3: by rewrite uleE to_uintD /#.
              - rewrite to_uintD /#.
           case (j = to_uint offset{1}) => [-> |?].
              - by rewrite ifT //= to_uintD /#.
              - rewrite ifF /=; first by rewrite to_uintD /#.     
                rewrite ifF 1:/#.
                have ->:  nth witness heights{2} j = nth witness (sub_list heights{2} 0 (to_uint offset{1})) j by rewrite /sub_list nth_mkseq 1:/#.
                rewrite -H18 (nth_map witness); first by rewrite size_sub /#.
                by rewrite nth_sub /#.
         - move => k??.
           rewrite !nth_put /#.
         - rewrite n_val; apply (eq_from_nth witness); first by rewrite size_sub 1:/# size_sub_list /#.
           rewrite size_sub 1:/# => j?.
           rewrite nth_sub 1:/# /= /sub_list nth_mkseq 1:/# /= /nbytes_flatten (nth_flatten witness n).
               * admit. (* Obs: Passei a frente para poupar tempo, sei resolver isto *)
           rewrite (nth_map witness); first by rewrite size_put /#.
           rewrite nth_put 1:/#.
           case (to_uint offset{1} = j %/ n) => H.
               * rewrite H24 get_to_list /= -H30 /#.
               * have ->: nth witness (val (nth witness stack{2} (j %/ n))) (j %% n) = nth witness (sub_list (nbytes_flatten stack{2}) 0 (n * to_uint offset{1})) j.
                   + rewrite /sub_list nth_mkseq 1:/# /= /nbytes_flatten (nth_flatten witness n).
                        - admit. (* Passei a frente para poupar tempo, eu sei resolver isto *)
                     by rewrite (nth_map witness) 1:/#.
                 rewrite -H20 nth_sub 1:/# /= /#.
         - smt().
         - move => ?; rewrite size_put.
           admit. (* Talvez aqui seja sub .. (offset - 1) *)

seq 1 0 : (
    #pre /\ 
    (cond{1} = W8.one) = (2 <= offset{2} /\ heights{1}.[to_uint offset{1} - 2] = heights{1}.[to_uint offset{1} - 1])
).
    + ecall {1} (p_treehash_condition_correct_eq heights{1} offset{1}).
      auto => /> &1 &2 /#.

seq 0 1 : (#pre /\ sub node_addr{1} 0 4 = sub address{2} 0 4).
    + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27.
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
           by rewrite H24 nth_sub.
         - case (i = 3) => //?. 
           do (rewrite ifF 1:/#).
           have ->: node_addr{1}.[i] = nth witness (sub node_addr{1} 0 3) i by rewrite nth_sub /#.
           by rewrite H12 nth_sub /#.

 
while (
  t{2} = to_uint target_height{1} /\ 0 <= t{2} <= h /\
  s{2} = to_uint start_index{1} /\0 <= s{2}  <= h /\

  0 <= offset{2} <= size heights{2} /\
  offset{2} = to_uint offset{1} /\
  (i{2} <> 0 => 0 < offset{2}) /\
  
  0 <= i{2} /\ i{2} < 2 ^ t{2} /\
  to_uint i{1} = i{2} /\
  to_uint upper_bound{1} = 2 ^ t{2} /\

  size stack{2} = h %/ d + 1 /\
  size heights{2} = h %/ d /\

  sk_seed{2} = (insubd (to_list sk_seed{1}))%NBytes /\
  pub_seed{2} = (insubd (to_list pub_seed{1}))%NBytes /\
  sub ots_addr{1} 0 3 = sub address{2} 0 3 /\
  
  sub ltree_addr{1} 0 3 = sub address{2} 0 3 /\
  sub node_addr{1} 0 3 = sub address{2} 0 3 /\
  ots_addr{1}.[3] = W32.zero /\
  ltree_addr{1}.[3] = W32.one /\
  node_addr{1}.[3] = (of_int 2)%W32 /\
  node_addr{1}.[4] = W32.zero /\

  map W32.to_uint (sub heights{1} 0 offset{2}) = sub_list heights{2} 0 offset{2} /\

  (forall (k : int), 0 <= k < offset{2} => 0 <= nth witness heights{2} k < XMSS_FULL_HEIGHT) /\

  sub _stack{1} 0 (n * offset{2}) = sub_list (nbytes_flatten stack{2}) 0 (n * offset{2}) /\

  (cond{1} = W8.one) <=> (2 <= offset{2} /\ heights{1}.[to_uint offset{1} - 2] = heights{1}.[to_uint offset{1} - 1])
); first by admit.


    + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 *.
      rewrite ultE in H20.
      do split.
          - smt(). 
          - smt().
          - rewrite H27 => [#] ?H.  
            split => [/# |].
            have ->: nth witness heights{2} (to_uint offset{1} - 2) = nth witness (sub_list heights{2} 0 (to_uint offset{1})) (to_uint offset{1} - 2) by rewrite /sub_list nth_mkseq /#.
            have ->: nth witness heights{2} (to_uint offset{1} - 1) = nth witness (sub_list heights{2} 0 (to_uint offset{1})) (to_uint offset{1} - 1) by rewrite /sub_list nth_mkseq /#.
            rewrite -H17.
            rewrite (nth_map witness); first by rewrite size_sub /#.
            rewrite nth_sub 1:/# /=.
            rewrite (nth_map witness); first by rewrite size_sub /#.
            rewrite nth_sub 1:/# /=.
            by rewrite H.
          - rewrite H27 => ?.
            have ->: nth witness heights{2} (to_uint offset{1} - 2) = nth witness (sub_list heights{2} 0 (to_uint offset{1})) (to_uint offset{1} - 2) by rewrite /sub_list nth_mkseq /#.
            have ->: nth witness heights{2} (to_uint offset{1} - 1) = nth witness (sub_list heights{2} 0 (to_uint offset{1})) (to_uint offset{1} - 1) by rewrite /sub_list nth_mkseq /#.
            rewrite -H17.
            rewrite (nth_map witness); first by rewrite size_sub /#.
            rewrite nth_sub 1:/# /=.
            rewrite (nth_map witness); first by rewrite size_sub /#.
            rewrite nth_sub 1:/# /=.
            move => H.
            split => [/#|].
            smt(@W32 pow2_32).
          - move => _stack_L cond_L heights_L node_addr_L offset_L address_R heights_R offset_R stack_R.
            move => H29 H30 H31.
            do split.
                + admit.
                + admit.
                + admit.
                + admit.
                + smt().
                + smt().
                + rewrite to_uintD_small //. 
                  admit.
                + admit.



              
           





    
     
