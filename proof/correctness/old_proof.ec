

do split.
     + smt().
     + smt().
     + move => H31 H32 result.
       rewrite /treehash_cond => H33.
       do split.
          * rewrite size_put /#.
          * admit. (* Tirar isto da pre do ciclo interior *)
          * rewrite size_put /#.
          * apply (eq_from_nth witness); first by rewrite size_map size_sub 1:/# size_sub_list /#.
            rewrite size_map size_sub 1:/# => i?.
            rewrite (nth_map witness).
                - rewrite size_sub /#.
            rewrite /sub_list nth_sub 1:/# nth_mkseq 1:/# /= nth_put 1:/# get_setE .
                - rewrite to_uintB 2:/# uleE /#.
            case (i = to_uint offset{1} - 1) => ?.
                - rewrite ifT.
                     + rewrite to_uintB 2:/# uleE /#.
                  rewrite ifT 1:/#. 
                  have ->: nth witness heights{2} (to_uint offset{1} - 1) = nth witness (sub_list heights{2} 0 (to_uint offset{1})) (to_uint offset{1} - 1).
                     + rewrite /sub_list nth_mkseq /#.
                  rewrite /sub_list nth_mkseq 1:/# /=. 
                  admit.
            rewrite ifF.
                - rewrite to_uintB 2:/# uleE /#.  
            rewrite ifF /#.
          * move => k*.
            rewrite nth_put /#.
          * move => k*.
            rewrite nth_put 1:/# get_setE.
                - rewrite to_uintB 2:/# uleE /#.
            case (k = to_uint offset{1} - 1) => [-> |?].
                - rewrite ifT.   
                     + rewrite to_uintB 2:/# uleE /#.
                   rewrite ifT //.           
                   have ->: to_uint (offset{1} - W64.one) = to_uint offset{1} - 1 by smt(@W64 pow2_64).
                   admit.
            admit.
          * smt().
          * rewrite !nth_put /#.
          * rewrite !nth_put 1,2:/#. 
            admit.
qed.  

