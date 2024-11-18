lemma impl_and_L (a b : bool) : (true => (a /\ b)) => a by [].
lemma impl_and_R (a b : bool) : (true => (a /\ b)) => b by [].
lemma false_eq (b : bool) : false = b => !b by [].

swap {1} 2 -1.

seq 1 2 : (
    #{/~sub ots_addr{1} 0 3 = sub address{2} 0 3}pre /\ sub ots_addr{1} 0 5 = sub address{2} 0 5
).
    + inline {1}; auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25. 
      rewrite /set_ots_addr /set_type.
      do split; (
         apply (eq_from_nth witness); [by rewrite !size_sub | rewrite size_sub // => i?];
         rewrite !nth_sub //= !get_setE //
      ).
         * do (rewrite ifF 1:/#).
           have ->: ltree_addr{1}.[i] = nth witness (sub ltree_addr{1} 0 3) i by rewrite nth_sub.
           by rewrite H21 nth_sub.
         * do (rewrite ifF 1:/#).
           have ->: node_addr{1}.[i] = nth witness (sub node_addr{1} 0 3) i by rewrite nth_sub.
           by rewrite H22 nth_sub.
         * case (i = 4) => ?.
              - by rewrite -H25 to_uintK.
              - do 3! (rewrite ifF 1:/#).
                case (i = 3) => [/# |?].
                have ->: ots_addr{1}.[i] = nth witness (sub ots_addr{1} 0 3) i by rewrite nth_sub /#.
                rewrite H20 nth_sub /#.

seq 1 0 : (#pre /\ ltree_addr{1}.[4] = W32.of_int (s{2} + i{2})).
    + inline {1}; auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 *.
      split.
         * apply (eq_from_nth witness); first by rewrite !size_sub.
           rewrite size_sub // => i?.
           rewrite !nth_sub // get_setE // ifF 1:/# /=.
           have ->: ltree_addr{1}.[i] = nth witness (sub ltree_addr{1} 0 3) i by rewrite nth_sub.
           by rewrite H20 nth_sub.
         * by rewrite -H24 to_uintK.

(* ========================================================================================================================================================= *)
seq 1 4 : (
  #{/~sub ots_addr{1} 0 5 = sub address{2} 0 5}
   {/~ltree_addr{1}.[4] = (of_int (s{2} + i{2}))%W32}pre /\
   val node{2} = to_list buf{1} /\ 
   sub ots_addr{1} 0 3 = sub address{2} 0 3
).
    + inline {1} M(Syscall).__gen_leaf_wots_ M(Syscall)._gen_leaf_wots M(Syscall).__gen_leaf_wots.             

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
           call {1} (pkgen_results P3 P4 P5 P6) => [/# |].
           auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 *.
           split => [| /#].
           move => k*.
           have ->: P5.[k] = nth witness (sub P5 0 5) k by rewrite nth_sub.
           rewrite H25 nth_sub /#.

      seq 0 2 : (
          #{/~sub ots_addr{1} 0 5 = sub address{2} 0 5}pre /\ 
          sub ltree_addr2{1} 0 5 = sub address{2} 0 5
      ).
         * auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 *.
           rewrite /set_ltree_addr /set_type.
           do split; (
              apply (eq_from_nth witness); [by rewrite !size_sub | rewrite size_sub // => i?];
              rewrite !nth_sub // !get_setE //=
           ).
               - do (rewrite ifF 1:/#).
                 have ->: ltree_addr{1}.[i] = nth witness (sub ltree_addr{1} 0 3) i by rewrite nth_sub.
                 by rewrite H20 nth_sub.
               - do (rewrite ifF 1:/#).
                 have ->: node_addr{1}.[i] = nth witness (sub node_addr{1} 0 3) i by rewrite nth_sub.
                 by rewrite H21 nth_sub.
               - case (i = 4) => [-> /# |?].
                 case (i = 3) => [-> /# |?].
                 do (rewrite ifF 1:/#).
                 have ->: ltree_addr{1}.[i] = nth witness (sub ltree_addr{1} 0 3) i by rewrite nth_sub /#.
                 by rewrite H20 nth_sub /#.
      
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

      auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 *.
      do split.
         * apply (eq_from_nth witness); first by rewrite !size_sub.
           rewrite size_sub // => i?. 
           rewrite !nth_sub /#.
         * by rewrite H31.
         * apply (eq_from_nth witness); first by rewrite !size_sub.
           rewrite size_sub // => i?. 
           rewrite !nth_sub /#.
(* ========================================================================================================================================================= *)
 
wp => /=. (* simplifies #post *)

seq 2 0 : (#pre /\ to_uint t64{1} = offset{2} * 32).
    + auto => /> &1 &2 *.
      rewrite to_uintM of_uintK /#.  

seq 3 3 : (
          #{/~offset{2} < size heights{2}}
           {/~to_uint t64{1} = offset{2} * 32}pre /\
           1 <= offset{2} <= size heights{2} 
).
    + wp.
      exists * _stack{1}, buf{1}, t64{1}; elim * => P3 P4 P5.
      call {1} (memcpy_u8u8_3_352_32_post P3 P4 P5).
      auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 *.
      do split; 1,2: by smt().
      move => ?? result H34 H35 H36. 
      do split.
          * rewrite to_uintD /#.
          * smt().
          * smt(). 
          * rewrite size_put /#.
          * by rewrite size_put.
          * apply (eq_from_nth witness); first by rewrite size_sub_list 1:/# size_map size_sub /#.
            rewrite size_map size_sub 1:/# => i?.
            rewrite (nth_map witness).
              - rewrite size_sub /#.
            rewrite nth_sub 1:/# /= /sub_list nth_mkseq 1:/# /= nth_put 1:/# get_setE.
              - smt(@W64 pow2_64).
            case (to_uint offset{1} = i) => [<- |?].
              - by rewrite ifT 1:#smt:(@W64 pow2_64).
              - rewrite ifF 1:#smt:(@W64 pow2_64).
                have ->: nth witness heights{2} i = nth witness (sub_list heights{2} 0 (to_uint offset{1})) i by rewrite /sub_list nth_mkseq 1:/#.
                rewrite -H13 (nth_map witness).
                  * rewrite size_sub /#.
                rewrite nth_sub /#.
          * apply (eq_from_nth witness); first by rewrite size_sub 1:/# size_sub_list /#.
            rewrite size_sub 1:/# => i?.
            rewrite nth_sub 1:/# /sub_list nth_mkseq 1:/# /= /nbytes_flatten (nth_flatten witness n).
              - pose P := (fun (s0 : W8.t list) => size s0 = n).
                pose L := (map NBytes.val  (put stack{2} (to_uint offset{1}) node{2})).
                rewrite -(all_nthP P L witness) /P /L size_map size_put H7 d_val h_val /= => j?.
                rewrite (nth_map witness); [rewrite size_put /# |].
                by rewrite valP.
            rewrite (nth_map witness).
              - rewrite size_put /#.
            rewrite nth_put 1:/#.
            case (to_uint offset{1} = i %/ n) => H.
              - rewrite H25 get_to_list -H35 /#.
              - rewrite H34 1:/#.
                have ->: P3.[i] = nth witness (sub P3 0 (n * to_uint offset{1})) i by rewrite nth_sub /#.
                rewrite H14 /sub_list nth_mkseq 1:/# /nbytes_flatten /= (nth_flatten witness n).
                  * pose P := (fun (s0 : W8.t list) => size s0 = n).
                    pose L := (map NBytes.val stack{2}).
                    rewrite -(all_nthP P L witness) /P /L size_map H7 d_val h_val /= => j?.
                    by rewrite (nth_map witness) 1:/# valP.
                by rewrite (nth_map witness) 1:/#.
          * smt(nth_put).
          * smt().
          * rewrite size_put /#.
 
conseq (: 
  t{2} = to_uint target_height{1} /\ 0 <= t{2} <= h /\ (* target height *)
  s{2} = to_uint start_index{1} /\ 0 <= s{2} <= h /\ (* start index *)
  offset{2} = to_uint offset{1} /\ (i{2} <> 0 => 0 < offset{2}) /\ (* offset *)
  size stack{2} = h %/ d + 1 /\  size heights{2} = h %/ d /\
  to_uint i{1} = i{2} /\ i{2} <= to_uint target_height{1} /\ 0 <= i{2} <= 2 ^ t{2} /\ (* i *)
  to_uint upper_bound{1} = 2 ^ t{2} /\
  sk_seed{2} = (insubd (to_list sk_seed{1}))%NBytes /\
  pub_seed{2} = (insubd (to_list pub_seed{1}))%NBytes /\
  val node{2} = to_list buf{1} /\ 

  ots_addr{1}.[3] = W32.zero /\        (* addr type *)
  ltree_addr{1}.[3] = W32.one /\       (* addr type *)
  node_addr{1}.[3] = (of_int 2)%W32 /\ (* addr type *)
  node_addr{1}.[4] = W32.zero /\       (* padding   *)

  sub ots_addr{1} 0 3   = sub address{2} 0 3 /\
  sub ltree_addr{1} 0 3 = sub address{2} 0 3 /\
  sub node_addr{1} 0 3  = sub address{2} 0 3 /\

  1 <= offset{2} /\ offset{2} <= size heights{2} (* other stuff *) /\

  map W32.to_uint (sub heights{1} 0 offset{2}) = sub_list heights{2} 0 offset{2} /\ (* <---- aparece em baixo como um forall => mais util em algumas provas *)
  sub _stack{1} 0 (n * offset{2})              = sub_list (nbytes_flatten stack{2}) 0 (n * offset{2}) /\

  (forall (k : int), 0 <= k < offset{2} => 0 <= nth witness heights{2} k < XMSS_FULL_HEIGHT) /\ 

  (forall (k : int), 0 <= k < offset{2} => W32.to_uint heights{1}.[k] = nth witness heights{2} k)
  ==> 
  _
).
    + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26?.
      move => k??.
      have ->: nth witness heights{2} k = nth witness (sub_list heights{2} 0 (to_uint offset{1})) k by rewrite /sub_list nth_mkseq /#.
      rewrite -H12 (nth_map witness).
         - rewrite size_sub /#.
      rewrite nth_sub /#.

seq 0 1 : (
    #{/~sub node_addr{1} 0 3 = sub address{2} 0 3}pre /\ 
    sub node_addr{1} 0 4 = sub address{2} 0 4 /\ 
    address{2}.[4] = W32.zero 
).
    + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23*.
      do split; (
            apply (eq_from_nth witness); 
                  [by rewrite !size_sub | rewrite size_sub // => i?];
                  rewrite /set_type !nth_sub //= !get_setE // 
      ).
        - do (rewrite ifF 1:/#).          
          have ->: address{2}.[i] = nth witness (sub address{2} 0 3) i by rewrite nth_sub.
          by rewrite -H16 nth_sub.
        - do (rewrite ifF 1:/#).
          have ->: address{2}.[i] = nth witness (sub address{2} 0 3) i by rewrite nth_sub.
          by rewrite -H17 nth_sub.
        - case (i = 3) => [/# | ?].
          have ->: address{2}.[i] = nth witness (sub address{2} 0 3) i by rewrite nth_sub /#.
          by rewrite -H18 nth_sub /#.
 
seq 1 0 : (
    #pre /\ 
    (((cond{1} = W8.one) => (2 <= offset{2} /\ heights{1}.[to_uint offset{1} - 2] = heights{1}.[to_uint offset{1} - 1]))) /\
    (((2 <= offset{2} /\ heights{1}.[to_uint offset{1} - 2] = heights{1}.[to_uint offset{1} - 1]) => (cond{1} = W8.one)))
).
    + ecall {1} (treehash_condition_correct heights{1} offset{1}).
      auto => /> &1 &2 /#.

 

while (#{/~val node{2} = to_list buf{1}}pre); last first.
    + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27.
      do split; first by smt().
        - move => Ha.
          have ->: nth witness heights{2} (to_uint offset{1} - 1) = nth witness (sub_list heights{2} 0 (to_uint offset{1})) (to_uint offset{1} - 1) by rewrite /sub_list nth_mkseq  /#.
          have ->: nth witness heights{2} (to_uint offset{1} - 2) = nth witness (sub_list heights{2} 0 (to_uint offset{1})) (to_uint offset{1} - 2) by rewrite /sub_list nth_mkseq  /#.
          rewrite -H20.
          do 2! (rewrite (nth_map witness); [by rewrite size_sub /# | rewrite nth_sub 1:/# /=]) => Hb.
          apply H27.
          split => //.
          smt(@W32 pow2_32).
        - move => _stack_L cond_L heights_L node_addr_L offset_L address_R heights_R stack_R. 
          move => H28 H29 H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 H40 H41 H42 H43 H44 H45. 
          do split.
             + smt().
             + smt().
             + admit. (* 0 <= to_uint offset_L => to_uint offset_L < size heights_R *)
             + smt().
             + smt(@W32 pow2_32 @IntDiv).
             + admit. (* FIXME: Esta hipotese e falsa ==> remover do invariante *) (* to_uint i{1} + 1 <= to_uint target_height{1} *)
             + rewrite to_uintD /#.
             + apply (eq_from_nth witness); first by rewrite !size_sub.
               rewrite size_sub // => i?.
               rewrite !nth_sub // ; smt(sub_k).
             + rewrite ultE; smt(@W32 pow2_32 @IntDiv).
             + rewrite ultE to_uintD /#.
 
seq 5 1 : (#pre /\ tree_idx{1} = tree_index{2}).
    + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 *. 
      rewrite (: 31 = 2^5 - 1) 1:/# and_mod // /(`>>`) to_uint_truncateu8.
      rewrite !of_uintK.
      congr; first by rewrite - to_uintK to_uintD_small 1:/#.
      have ->: to_uint (heights{1}.[to_uint (offset{1} - W64.one)] + W32.one) = nth witness heights{2} (to_uint offset{1} - 1) + 1; last by smt(modz_small).
      have ->: nth witness heights{2} (to_uint offset{1} - 1) = nth witness (sub_list heights{2} 0 (to_uint offset{1})) (to_uint offset{1} - 1) by rewrite /sub_list nth_mkseq /#.
      rewrite -H19 (nth_map witness).
         * rewrite size_sub /#.
      rewrite nth_sub 1:/# /=.
      have ->: to_uint (offset{1} - W64.one) = to_uint offset{1} - 1 by smt(@W64 pow2_64). (* This smt fails sometimes *)
      rewrite to_uintD /#.

seq 2 2 : (#pre /\ sub node_addr{1} 0 7 = sub address{2} 0 7).
    + inline {1}. auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 *.
      rewrite /set_tree_height /set_tree_index.
      do split; (
             apply (eq_from_nth witness); [by rewrite !size_sub | rewrite size_sub // => i?]; 
             rewrite !nth_sub // get_setE //
      ).
         * rewrite ifF 1:/# /= get_setE // ifF 1:/# /=.
           have ->: ots_addr{1}.[i] = nth witness (sub ots_addr{1} 0 3) i by rewrite nth_sub.
           by rewrite H15 nth_sub.
         * rewrite ifF 1:/# /= get_setE // ifF 1:/# /=.
           have ->: ltree_addr{1}.[i] = nth witness (sub ltree_addr{1} 0 3) i by rewrite nth_sub.
           by rewrite H16 nth_sub.
         * rewrite ifF 1:/# /= get_setE // ifF 1:/# /=.
           rewrite get_setE // ifF 1:/# get_setE // ifF 1:/#.
           have ->: node_addr{1}.[i] = nth witness (sub node_addr{1} 0 4) i by rewrite nth_sub.
           by rewrite H23 nth_sub.
         * rewrite get_setE //.
           case (i = 6) => [-> // |?].
           rewrite ifF //.
           case (i = 5) => [-> //= |?].
              - have ->: to_uint (offset{1} - W64.one) = to_uint offset{1} - 1 by smt(@W64 pow2_64). (* Obs: this smt fails sometimes *)
                have ->: (nth witness heights{2} (to_uint offset{1} - 1)) = nth witness (sub_list heights{2} 0 (to_uint offset{1})) (to_uint offset{1} - 1) by rewrite /sub_list nth_mkseq 1:/#.
                rewrite -H19 (nth_map witness); [rewrite size_sub /# |].
                by rewrite nth_sub 1:/# to_uintK.    
           case (i = 4) => [-> /= | ?].
              - by rewrite H14 H24.
           rewrite ifF 1:/# get_setE // ifF 1:/# get_setE // ifF 1:/# /=.
           have ->: node_addr{1}.[i] = nth witness (sub node_addr{1} 0 4) i by rewrite nth_sub // /#.
           rewrite H23 nth_sub //#.

seq 3 0 : (#pre /\ to_uint t64{1} = (offset{2} - 2) * 32).
          + auto => /> &1 &2 *.
            rewrite to_uintM to_uintB 2:/# uleE /#.

seq 1 2 : (#pre /\ to_list buf2{1} = val node0{2} ++ val node1{2}).
          + wp.
            ecall {1} (memcpy_u8u8_2_64_352_post buf2{1} _stack{1} t64{1}).
            skip => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 result ->.
            apply (eq_from_nth witness); first by rewrite size_cat size_sub // !valP n_val.
            rewrite size_sub // => i?.
            rewrite nth_sub //.
            case (0 <= i < 32) => ?.
               - rewrite nth_cat valP ifT 1:/#.
                 have ->: _stack{1}.[to_uint t64{1} + i] = nth witness (sub _stack{1} 0 (n * to_uint offset{1})) (to_uint t64{1} + i) by rewrite nth_sub 1:/# /=.
                 rewrite H20 /sub_list nth_mkseq 1:/# /= /nbytes_flatten (nth_flatten witness n).
                    + pose P := (fun (s0 : W8.t list) => size s0 = n).
                      pose L := (map NBytes.val stack{2}).
                      rewrite -(all_nthP P L witness) /P /L size_map H5 => j?.
                      by rewrite (nth_map witness) 1:/# valP.
                 rewrite (nth_map witness) 1:/# H29 /#.                     
            (* At this point, 32 <= i < 64 *)
            rewrite nth_cat valP ifF 1:/#.
                 have ->: _stack{1}.[to_uint t64{1} + i] = nth witness (sub _stack{1} 0 (n * to_uint offset{1})) (to_uint t64{1} + i) by rewrite nth_sub 1:/# /=.
                 rewrite H20 /sub_list nth_mkseq 1:/# /= /nbytes_flatten (nth_flatten witness n).
                    + pose P := (fun (s0 : W8.t list) => size s0 = n).
                      pose L := (map NBytes.val stack{2}).
                      rewrite -(all_nthP P L witness) /P /L size_map H5 => j?.
                      by rewrite (nth_map witness) 1:/# valP.
                 rewrite (nth_map witness) 1:/# H29 /#.    

seq 1 1 : (#{/~val node{2} = to_list buf{1}}pre /\ val new_node{2} = to_list buf{1}).
          + inline {1} M(Syscall).__thash_h_ M(Syscall)._thash_h; wp; sp.
            exists * node0{2}, node1{2}, pub_seed1{1}, addr0{1}, address{2}.
            elim * => P0 P1 P2 P3 P4. 
            call (rand_hash_results P0 P1 P2 P3 P4) => [/# |].
            skip => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H29 H30 H31. 
            do split.
               * rewrite /merge_nbytes_to_array tP => j?.
                 rewrite initiE //=.
                 by case (0 <= j < 32) => ?; rewrite -get_to_list H31 nth_cat valP n_val; [rewrite ifT 1:/# | rewrite ifF 1:/#].
               * smt(sub_k).
               * move => H32 H33 resultImpl resultSpec H34 H35.
                 do split.
                    - smt().
                    - by rewrite H35.
                    - apply (eq_from_nth witness); first by rewrite !size_sub. 
                      rewrite size_sub // => i?. 
                      rewrite !nth_sub //#. 
                    - apply (eq_from_nth witness); first by rewrite !size_sub. 
                      rewrite size_sub // => i?. 
                      rewrite !nth_sub //#. 
                    - by rewrite H34.

seq 5 2 : (#{/~val new_node{2} = to_list buf{1}}pre).
          + wp. 
            ecall {1} (memcpy_u8u8_3_352_32_post _stack{1} buf{1} t64{1}).
            auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31.
            do split.
              * rewrite to_uintM of_uintK /=.
                smt(@W64 pow2_64).
              * rewrite to_uintM of_uintK /=.
                smt(@W64 pow2_64).
              * move => H32 H33 stackRes.  
                have ->: to_uint ((offset{1} - (of_int 2)%W64) * (of_int 32)%W64) = (to_uint offset{1} - 2) * 32 by rewrite to_uintM of_uintK /=; smt(@W64 pow2_64). 
                move => H34 H35 H36. 
                do split.
                     - rewrite to_uintB 2:/# uleE /#.
                     - smt().
                     - rewrite size_put /#.
                     - smt().
                     - smt().
                     - apply (eq_from_nth witness); first by rewrite size_map size_sub 1:/# size_sub_list /#.
                       rewrite size_map size_sub 1:/# => i?.
                       rewrite (nth_map witness). 
                             + rewrite size_sub /#.
                       rewrite nth_sub 1:/# /=.
                       have ->: to_uint heights{1}.[i] = nth witness (map W32.to_uint (sub heights{1} 0 (to_uint offset{1}))) i.
                             + rewrite (nth_map witness); [by rewrite size_sub /# |].
                               rewrite nth_sub /#.
                       rewrite H19 /sub_list !nth_mkseq /#.
                     - apply (eq_from_nth witness); first by rewrite size_sub 1:/# size_sub_list /#.
                       rewrite size_sub 1:/# => i?.
                       rewrite nth_sub 1:/# /= /sub_list nth_mkseq 1:/# /nbytes_flatten /= (nth_flatten witness n).
                             + pose P := (fun (s0 : W8.t list) => size s0 = n).
                               pose L := (map NBytes.val (put stack{2} (to_uint offset{1} - 2) new_node{2})). 
                               rewrite -(all_nthP P L witness) /P /L size_map size_put H5 => j?.
                               rewrite (nth_map witness).
                                    * rewrite size_put /#.
                               by rewrite valP.
                       rewrite (nth_map witness) 1:#smt:(size_put) nth_put 1:/#.
                       case (to_uint offset{1} - 2 = i %/ n) => ?.
                             + rewrite H31 get_to_list /#.
                       rewrite H34 1:/#.
                       have ->: _stack{1}.[i] = nth witness (sub _stack{1} 0 (n * to_uint offset{1})) i by rewrite nth_sub /#.
                       rewrite H20 /sub_list nth_mkseq 1:/# /= /nbytes_flatten (nth_flatten witness n).
                             + pose P := (fun (s0 : W8.t list) => size s0 = n).
                               pose L := (map NBytes.val stack{2}). 
                               rewrite -(all_nthP P L witness) /P /L size_map H5 => j?.
                               by rewrite (nth_map witness) 1:/# valP n_val.
                       rewrite (nth_map witness) /#.
                     - smt().
                     - smt().
                     - admit. (* 2 <= to_uint offset{1} - 1 ==> Experimentar meter isto no invariante do ciclo interior *)
                     - have ->: to_uint (offset{1} - W64.one) = to_uint offset{1} - 1 by rewrite to_uintB 2:/# uleE /#.
                       simplify.
                       admit.
                     - admit.
                     - 
 


                     - admit. (* 2 <= to_uint offset{1} - 1 *)
                     - admit.



































(* Remove redundant statement in #post *) 
conseq (: 
  _ 
  ==>
  t{2} = to_uint target_height{1} /\
  0 <= t{2} /\
  t{2} <= h /\
  s{2} = to_uint start_index{1} /\
  0 <= s{2} /\
  s{2} <= h /\
  offset{2} = to_uint offset{1} /\
  (i{2} + 1 <> 0 => 0 < offset{2}) /\
  0 <= offset{2} /\
  offset{2} < size heights{2} /\
  size stack{2} = h %/ d + 1 /\
  size heights{2} = h %/ d /\
  0 <= i{2} + 1 /\
  i{2} + 1 <= 2 ^ t{2} /\
  i{2} + 1 <= to_uint target_height{1} /\
  to_uint i{1} + 1 = i{2} + 1 /\
  to_uint upper_bound{1} = 2 ^ t{2} /\
  sk_seed{2} = (insubd (to_list sk_seed{1}))%NBytes /\
  pub_seed{2} = (insubd (to_list pub_seed{1}))%NBytes /\
  map W32.to_uint (sub heights{1} 0 offset{2}) = sub_list heights{2} 0 offset{2} /\
  sub _stack{1} 0 (n * offset{2}) = sub_list (nbytes_flatten stack{2}) 0 (n * offset{2}) /\
  (forall (k : int), 0 <= k < offset{2} => 0 <= nth witness heights{2} k < XMSS_FULL_HEIGHT) /\
  ots_addr{1}.[3] = W32.zero /\
  ltree_addr{1}.[3] = W32.one /\
  node_addr{1}.[3] = (of_int 2)%W32 /\
  node_addr{1}.[4] = W32.zero /\
  sub ots_addr{1} 0 3 = sub address{2} 0 3 /\
  sub ltree_addr{1} 0 3 = sub address{2} 0 3 /\
  sub node_addr{1} 0 3 = sub address{2} 0 3
); last by admit.
auto => &1 &2 *.
do split.
smt().
smt().
smt().
smt().
smt().
smt().
smt().
smt().
smt().
smt().
smt().
smt().
smt().
smt().
smt().
rewrite to_uintD /#.
smt().
smt().
smt().
smt().
smt().
smt().
smt().
smt().
smt().
smt().
smt().
smt().
smt().
rewrite ultE. smt(pow2_bound).
 /#.
smt().
smt().
smt().
smt().
smt().
smt().

smt(pow2_bound).


(* ========================================================= tou aqui *)
 
while (#{/~val node{2} = to_list buf{1}}pre); first by admit.
    + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26.
      do split.
        - smt().
        - move => Ha.
          have ->: nth witness heights{2} (to_uint offset{1} - 1) = nth witness (sub_list heights{2} 0 (to_uint offset{1})) (to_uint offset{1} - 1) by rewrite /sub_list nth_mkseq  /#.
          have ->: nth witness heights{2} (to_uint offset{1} - 2) = nth witness (sub_list heights{2} 0 (to_uint offset{1})) (to_uint offset{1} - 2) by rewrite /sub_list nth_mkseq  /#.
          rewrite -H20.
          do 2! (rewrite (nth_map witness); [by rewrite size_sub /# | rewrite nth_sub 1:/# /=]) => Hb.
          apply H26.
          split => //.
          smt(@W32 pow2_32).
        - move => _stack_L cond_L heights_L node_addr_L offset_L address_R heights_R stack_R. 
          move => H27 H28 H29 H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 H40 H41 H42 H43. 
          do split.
            + smt().
            + smt().
            + admit. (* to_uint offset_L < size heights_R ====> offset e < na #post mas <= na pre *)
            + smt().
            + admit. (* to_uint i{1} + 1 <= 2 ^ to_uint target_height{1} *)
            + admit. (* to_uint i{1} + 1 <= to_uint target_height{1} *)
            +
























































































while (
    (* Obs: This invariant is the same as #{/~val node{2} = to_list buf{1}}pre *)
    (* O i nao esta entre 0 e 2^t fechado. Esta entre 0 e 2^t aberto pq i+=1 so e feito depois deste ciclo terminar *)

    0 <= t{2} <= h /\
    t{2} = to_uint target_height{1} /\
    to_uint upper_bound{1} = 2 ^ t{2} /\
  
    s{2} = to_uint start_index{1} /\
    0 <= s{2} <= h /\
  
    offset{2} = to_uint offset{1} /\
    (i{2} <> 0 => 0 < offset{2}) /\
    1 <= offset{2} <= size heights{2} /\ (* This comes from the invariant of the outer loop *)

    size stack{2} = h %/ d + 1 /\
    size heights{2} = h %/ d /\

    to_uint i{1} = i{2} /\
    i{2} <= to_uint target_height{1} /\
    0 <= i{2} <= 2 ^ t{2} /\
    
    sk_seed{2} = (insubd (to_list sk_seed{1}))%NBytes /\
    pub_seed{2} = (insubd (to_list pub_seed{1}))%NBytes /\
  
    ots_addr{1}.[3] = W32.zero /\
    ltree_addr{1}.[3] = W32.one /\
    node_addr{1}.[3] = (of_int 2)%W32 /\
    node_addr{1}.[4] = W32.zero /\
    sub ots_addr{1} 0 3 = sub address{2} 0 3 /\
    sub ltree_addr{1} 0 3 = sub address{2} 0 3 /\
    sub node_addr{1} 0 4 = sub address{2} 0 4 /\

    map W32.to_uint (sub heights{1} 0 offset{2}) = sub_list heights{2} 0 offset{2} /\
    sub _stack{1} 0 (n * offset{2}) = sub_list (nbytes_flatten stack{2}) 0 (n * offset{2}) /\

    (forall (k : int), 0 <= k < offset{2} => 0 <= nth witness heights{2} k && nth witness heights{2} k < XMSS_FULL_HEIGHT) /\
    (forall (k : int), 0 <= k < offset{2} => to_uint heights{1}.[k] = nth witness heights{2} k) /\

    (cond{1} = W8.one) = (2 <= offset{2} /\ heights{1}.[to_uint offset{1} - 2] = heights{1}.[to_uint offset{1} - 1])
); last first.
          + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25.
            do split. 
               - smt().
               - move => H27 H28. 
                 rewrite H25. 
                 split => [/# |].
                 have ->: heights{1}.[to_uint offset{1} - 2] = W32.of_int (nth witness heights{2} (to_uint offset{1} - 2)).
                    * have ->: heights{1}.[to_uint offset{1} - 2] = W32.of_int (nth witness (map W32.to_uint (sub heights{1} 0 (to_uint offset{1}))) (to_uint offset{1} - 2)).
                         + rewrite (nth_map witness); [rewrite size_sub /# | by rewrite nth_sub 1:/#].
                      by rewrite H20 /sub_list nth_mkseq 1:/#.
                 have ->: heights{1}.[to_uint offset{1} - 1] = W32.of_int (nth witness heights{2} (to_uint offset{1} - 1)).
                    * have ->: heights{1}.[to_uint offset{1} - 1] = W32.of_int (nth witness (map W32.to_uint (sub heights{1} 0 (to_uint offset{1}))) (to_uint offset{1} - 1)).
                         + rewrite (nth_map witness); [rewrite size_sub /# | by rewrite nth_sub 1:/#].
                      by rewrite H20 /sub_list nth_mkseq 1:/#.
                 rewrite H28 /#.
               - move => stackImpl condImpl heightsImpl node_addr offsetImpl addrSpec heightsSpec stackSpec.
                 move => H28 H29 H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 H40 H41 H42 H43 H44 *. 




                 do split.
                    * smt().
                    * smt().
                    * rewrite H34 d_val h_val /=. admit.
                    * smt(). 
                    * smt(@W64 pow2_64 @IntDiv). 
                    * admit.
                    * rewrite to_uintD /#.
                    * apply (eq_from_nth witness); first by rewrite !size_sub.
                      rewrite size_sub // => i?.
                      rewrite !nth_sub //=.
                      have ->: node_addr.[i] = nth witness (sub node_addr 0 4) i by rewrite nth_sub /#.
                      rewrite H43 nth_sub /#.
                    * rewrite ultE to_uintD_small 1:/# /= /#. 
                    * rewrite ultE to_uintD_small 1:/# /= /#. 
               
seq 5 1 : (#pre /\ tree_idx{1} = tree_index{2}).
    + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 *. 
      rewrite (: 31 = 2^5 - 1) 1:/# and_mod // /(`>>`) to_uint_truncateu8.
      rewrite !of_uintK.
      congr; first by rewrite - to_uintK to_uintD_small 1:/#.
      have ->: to_uint (heights{1}.[to_uint (offset{1} - W64.one)] + W32.one) = nth witness heights{2} (to_uint offset{1} - 1) + 1; last by smt(modz_small).
      have ->: nth witness heights{2} (to_uint offset{1} - 1) = nth witness (sub_list heights{2} 0 (to_uint offset{1})) (to_uint offset{1} - 1) by rewrite /sub_list nth_mkseq /#.
      rewrite -H19 (nth_map witness).
         * rewrite size_sub /#.
      rewrite nth_sub 1:/# /=.
      have ->: to_uint (offset{1} - W64.one) = to_uint offset{1} - 1 by smt(@W64 pow2_64). (* This smt fails sometimes *)
      rewrite to_uintD /#.

seq 2 2 : (#pre /\ sub node_addr{1} 0 7 = sub address{2} 0 7).
    + inline {1}. auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25.
      rewrite /set_tree_height /set_tree_index.
      do split; (
             apply (eq_from_nth witness); [by rewrite !size_sub | rewrite size_sub // => i?]; 
             rewrite !nth_sub // get_setE //
      ).
         * rewrite ifF 1:/# /= get_setE // ifF 1:/#.
           have ->: ots_addr{1}.[i] = nth witness (sub ots_addr{1} 0 3) i by rewrite nth_sub.
           by rewrite H14 nth_sub.
         * rewrite ifF 1:/# /= get_setE // ifF 1:/#.
           have ->: ltree_addr{1}.[i] = nth witness (sub ltree_addr{1} 0 3) i by rewrite nth_sub.
           by rewrite H15 nth_sub.
         * rewrite ifF 1:/# /= get_setE // ifF 1:/#.
           rewrite get_setE // ifF 1:/# get_setE // ifF 1:/#.
           have ->: node_addr{1}.[i] = nth witness (sub node_addr{1} 0 4) i by rewrite nth_sub.
           by rewrite H22 nth_sub.
         * rewrite get_setE //.
           case (i = 6) => [-> // |?].
           rewrite ifF //.
           case (i = 5) => [-> //= |?].
              - have ->: to_uint (offset{1} - W64.one) = to_uint offset{1} - 1 by smt(@W64 pow2_64). (* Obs: this smt fails sometimes *)
                have ->: (nth witness heights{2} (to_uint offset{1} - 1)) = nth witness (sub_list heights{2} 0 (to_uint offset{1})) (to_uint offset{1} - 1) by rewrite /sub_list nth_mkseq 1:/#.
                rewrite -H18 (nth_map witness); [rewrite size_sub /# |].
                by rewrite nth_sub 1:/# to_uintK.    
           case (i = 4) => [-> /= | ?].
              - admit. (* FIXME: Need more info here ==> from the precondition of the equiv *)
           rewrite ifF 1:/# get_setE // ifF 1:/# get_setE // ifF 1:/# /=.
           have ->: node_addr{1}.[i] = nth witness (sub node_addr{1} 0 4) i by rewrite nth_sub // /#.
           rewrite H22 nth_sub //#.

seq 3 0 : (#pre /\ to_uint t64{1} = (offset{2} - 2) * 32).
          + auto => /> &1 &2 *.
            rewrite to_uintM to_uintB 2:/# uleE /#.

seq 1 2 : (#pre /\ to_list buf2{1} = val node0{2} ++ val node1{2}).
          + wp.
            ecall {1} (memcpy_u8u8_2_64_352_post buf2{1} _stack{1} t64{1}).
            skip => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 result ->.
            (* Obs: A seta refere se a hipotese to_list result.`1 = sub _stack{1} (to_uint t64{1}) 64 *)
            apply (eq_from_nth witness); first by rewrite size_cat size_sub // !valP n_val.
            rewrite size_sub // => i?.
            rewrite nth_sub //.
            case (0 <= i < 32) => ?.
               - rewrite nth_cat valP ifT 1:/#.
                 have ->: _stack{1}.[to_uint t64{1} + i] = nth witness (sub _stack{1} 0 (n * to_uint offset{1})) (to_uint t64{1} + i) by rewrite nth_sub 1:/# /=.
                 rewrite H19 /sub_list nth_mkseq 1:/# /= /nbytes_flatten (nth_flatten witness n).
                    + pose P := (fun (s0 : W8.t list) => size s0 = n).
                      pose L := (map NBytes.val stack{2}).
                      rewrite -(all_nthP P L witness) /P /L size_map H5 => j?.
                      by rewrite (nth_map witness) 1:/# valP.
                 rewrite (nth_map witness) 1:/# H27 /#.                     
            (* At this point, 32 <= i < 64 *)
            rewrite nth_cat valP ifF 1:/#.
                 have ->: _stack{1}.[to_uint t64{1} + i] = nth witness (sub _stack{1} 0 (n * to_uint offset{1})) (to_uint t64{1} + i) by rewrite nth_sub 1:/# /=.
                 rewrite H19 /sub_list nth_mkseq 1:/# /= /nbytes_flatten (nth_flatten witness n).
                    + pose P := (fun (s0 : W8.t list) => size s0 = n).
                      pose L := (map NBytes.val stack{2}).
                      rewrite -(all_nthP P L witness) /P /L size_map H5 => j?.
                      by rewrite (nth_map witness) 1:/# valP.
                 rewrite (nth_map witness) 1:/# H27 /#.    

seq 1 1 : (#{/~val node{2} = to_list buf{1}}pre /\ val new_node{2} = to_list buf{1}).
          + inline {1} M(Syscall).__thash_h_ M(Syscall)._thash_h; wp; sp.
            exists * node0{2}, node1{2}, pub_seed1{1}, addr0{1}, address{2}.
            elim * => P0 P1 P2 P3 P4. 
            call (rand_hash_results P0 P1 P2 P3 P4) => [/# |].
            skip => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28. 
            do split.
               * rewrite /merge_nbytes_to_array tP => j?.
                 rewrite initiE //=.
                 by case (0 <= j < 32) => ?; rewrite -get_to_list H28 nth_cat valP n_val; [rewrite ifT 1:/# | rewrite ifF 1:/#].
               * smt(sub_k).
               * move => H32 H33 resultImpl resultSpec H34 H35.
                 do split.
                    - smt().
                    - apply (eq_from_nth witness); first by rewrite !size_sub. 
                      rewrite size_sub // => i?. 
                      rewrite !nth_sub //#. 
                    - apply (eq_from_nth witness); first by rewrite !size_sub. 
                      rewrite size_sub // => i?. 
                      rewrite !nth_sub //#. 
                    - by rewrite H34.
          
seq 5 2 : (#{/~val new_node{2} = to_list buf{1}}pre).
          + wp. 
            ecall {1} (memcpy_u8u8_3_352_32_post _stack{1} buf{1} t64{1}).
            auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29.
            do split.
              * rewrite to_uintM of_uintK /=.
                smt(@W64 pow2_64).
              * rewrite to_uintM of_uintK /=.
                smt(@W64 pow2_64).
              * move => H32 H33 stackRes.  
                have ->: to_uint ((offset{1} - (of_int 2)%W64) * (of_int 32)%W64) = (to_uint offset{1} - 2) * 32 by rewrite to_uintM of_uintK /=; smt(@W64 pow2_64). 
                move => H34 H35 H36. 
                do split.
                     - rewrite to_uintB 2:/# uleE /#.
                     - smt().
                     - rewrite size_put /#.
                     - smt().
                     - smt().
                     - apply (eq_from_nth witness); first by rewrite size_map size_sub 1:/# size_sub_list /#.
                       rewrite size_map size_sub 1:/# => i?.
                       rewrite (nth_map witness). 
                             + rewrite size_sub /#.
                       rewrite nth_sub 1:/# /=.
                       have ->: to_uint heights{1}.[i] = nth witness (map W32.to_uint (sub heights{1} 0 (to_uint offset{1}))) i.
                             + rewrite (nth_map witness); [by rewrite size_sub /# |].
                               rewrite nth_sub /#.
                       rewrite H18 /sub_list !nth_mkseq /#.
                     - apply (eq_from_nth witness); first by rewrite size_sub 1:/# size_sub_list /#.
                       rewrite size_sub 1:/# => i?.
                       rewrite nth_sub 1:/# /= /sub_list nth_mkseq 1:/# /nbytes_flatten /= (nth_flatten witness n).
                             + pose P := (fun (s0 : W8.t list) => size s0 = n).
                               pose L := (map NBytes.val (put stack{2} (to_uint offset{1} - 2) new_node{2})). 
                               rewrite -(all_nthP P L witness) /P /L size_map size_put H5 => j?.
                               rewrite (nth_map witness).
                                    * rewrite size_put /#.
                               by rewrite valP.
                       rewrite (nth_map witness) 1:#smt:(size_put) nth_put 1:/#.
                       case (to_uint offset{1} - 2 = i %/ n) => ?.
                             + rewrite H29 get_to_list /#.
                       rewrite H34 1:/#.
                       have ->: _stack{1}.[i] = nth witness (sub _stack{1} 0 (n * to_uint offset{1})) i by rewrite nth_sub /#.
                       rewrite H19 /sub_list nth_mkseq 1:/# /= /nbytes_flatten (nth_flatten witness n).
                             + pose P := (fun (s0 : W8.t list) => size s0 = n).
                               pose L := (map NBytes.val stack{2}). 
                               rewrite -(all_nthP P L witness) /P /L size_map H5 => j?.
                               by rewrite (nth_map witness) 1:/# valP n_val.
                       rewrite (nth_map witness) /#.
                     - smt().
                     - smt().
                     - admit. 
                     - admit. 
                     - admit.
                     - admit.
 
(* ========== tou aqui *)

ecall {1} (treehash_condition_correct heights{1} offset{1}).
auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28. 
have E0: heights{1}.[to_uint offset{1} - 2] = heights{1}.[to_uint offset{1} - 1] by have := H24; smt(impl_and_R).
do split; 1,2: by smt().
rewrite /treehash_cond => ?? cond_result H29.
do split.
    + rewrite size_put /#.
    + rewrite size_put /#.
    + apply (eq_from_nth witness); first by rewrite size_map size_sub 1:/# size_sub_list /#.
      rewrite size_map size_sub 1:/# => i?.
      rewrite (nth_map witness).
         - by rewrite size_sub /#.
      rewrite nth_sub 1:/# /= /sub_list nth_mkseq 1:/# /= nth_put 1:/#.
      have E: heights{1}.[to_uint offset{1} - 2] = heights{1}.[to_uint offset{1} - 1] by have := H23 => /#. 
      admit.
    + admit. (* Obs: smt(nth_put used to solve this goal *)
    + move => k??.
      rewrite get_setE_to_list.
        -  rewrite size_to_list to_uintB 2:/# uleE /#.
      rewrite nth_put.
        -  rewrite size_to_list to_uintB 2:/# uleE /#.
      rewrite nth_put 1:/#.
      have ->: to_uint (offset{1} - W64.one) = to_uint offset{1} - 1 by rewrite to_uintB 2:/# uleE /#.
      case (k = to_uint offset{1} - 1) => [-> /=|?].
        - have ->: nth witness heights{2} (to_uint offset{1} - 1) = nth witness (sub_list heights{2} 0 (to_uint offset{1})) (to_uint offset{1} - 1) by rewrite /sub_list nth_mkseq /#.
          rewrite -H18 (nth_map witness).
             * rewrite size_sub /#.
          rewrite nth_sub 1:/# /= to_uintD_small /#.
      rewrite ifF 1:/# ifF 1:/# get_to_list. 
      have ->: nth witness heights{2} k = nth witness (sub_list heights{2} 0 (to_uint offset{1})) k by rewrite /sub_list nth_mkseq /#.  
      rewrite -H18 (nth_map witness).
        - rewrite size_sub /#.
      rewrite nth_sub /#. 
    + rewrite get_setE_to_list. 
        - rewrite size_to_list to_uintB 2:/# uleE /#.
      rewrite !nth_put.
        - rewrite size_to_list to_uintB 2:/# uleE /#.
      rewrite ifF.
        - rewrite to_uintB 2:/# uleE /#.  
      rewrite get_to_list.
      have ->: to_uint (offset{1} - W64.one) = to_uint offset{1} - 1 by rewrite to_uintB 2:/# uleE /#.  
      admit.
    + rewrite H29.
      admit.
    + rewrite nth_put 1:/# nth_put 1:/# ifT // ifF 1:/# /#.
qed.


     


