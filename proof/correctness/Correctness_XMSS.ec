pragma Goals : printall.

require import AllCore List RealExp IntDiv Distr DList.
from Jasmin require import JModel JArray.

require import Types Params Parameters Address Notation Hash Primitives Wots XMSS_MT_PRF.
require import XMSS_IMPL.
require import Repr. 

require import Array4 Array8 Array32 Array64 Array68 Array96 Array132 Array136 Array352 Array2144.
require import WArray32 WArray96 WArray136.

require import Correctness_Address Correctness_Mem Correctness_Hash.
require import Utils DistrUtils.

require import BitEncoding.
(*---*) import BitChunking.

require import Termination.

(*** Treehash kg ***)

lemma treehash_kg_correct :
    equiv [
      M(Syscall).__treehash ~ TreeHash.treehash :
      true
      ==>
      to_list res{1}.`1 = res{2}.`1 
    ].
proof.
proc.
seq 7 0 : (#pre); first by auto.
admit.
qed.

(*** Key Gen ***)

clone import DListProgramX as T
  with type t <- W8.t,
       op d <- W8.dword.

(*** Keygen without OID ***)
lemma xmss_kg_no_oid : 
    n = XMSS_N /\ 
    d = XMSS_D =>
    equiv [
      M(Syscall).__xmssmt_core_keypair ~ XMSS_MT_PRF.kg :
      true 
      ==>
      res{2}.`1 = EncodeSkNoOID res{1}.`2 /\
      res{2}.`2 = EncodePkNoOID res{1}.`1
    ].
proof.
rewrite /XMSS_N /XMSS_D => [#] *. 
proc. 
seq 3 6 : (true); first by auto. 
swap {2} [3..5] -2. 
seq 1 3 : (
  to_list seed_p{1} = sk_seed{2} ++ sk_prf{2} ++ pub_seed{2} /\
  size sk_seed{2} = 32 /\
  size sk_prf{2} = 32 /\
  size pub_seed{2} = 32 
).
  + inline {1}; wp; sp; auto => />. 
    transitivity {2} { pub_seed <$ dlist W8.dword 96; }
    (true ==> to_list a{1} = pub_seed{2})
    (true ==> pub_seed{1} = (sk_seed{2} ++ sk_prf{2} ++ pub_seed{2}) /\ size sk_seed{2} = 32 /\
  size sk_prf{2} = 32 /\
  size pub_seed{2} = 32 ) => //.
        - rnd Array96.to_list (Array96.of_list W8.zero): *0 *0.
          auto => />;  split => [l | ?].
             * rewrite supp_dmap; move => [x].
               rewrite supp_dlist // => /> E _.
               by rewrite of_listK.
          split => [l | ?].
             * rewrite supp_dmap; move=> [x].                
               rewrite darray_dlist dmap_comp /(\o) /= supp_dlist //; move=> [[Ex Hx] ->].
               rewrite dmap_id dmap1E /(\o) /pred1 /=.
               apply mu_eq_support => y.
               rewrite supp_dlist //=; move=> [Ey Hy].
               rewrite eqboolP; split => //.
               move => E.
               by rewrite -(Array96.of_listK W8.zero y) // E of_listK.
          move => a; rewrite darray_dlist dmap_comp supp_dmap.              
          move => [l]; rewrite supp_dlist // => [[[Esz] H]].
          rewrite /(\o) /= => ->.
          by rewrite of_listK //= dmap_id supp_dlist //.
        (* At this point we're only working with distributions over lists *)
        - outline {1} [1] { pub_seed <@ T.Program.Sample.sample(96); }.
          transitivity {1} { pub_seed <@ T.SampleX.samplecat(64,32); }
          (true ==> ={pub_seed})
          (true ==> pub_seed{1} = sk_seed{2} ++ sk_prf{2} ++ pub_seed{2} /\ 
                    size sk_seed{2} = 32 /\ size sk_prf{2} = 32 /\ size pub_seed{2} = 32) => //.
             * by call sample_samplecat => //.
          inline*; swap {1} 2 1.
          seq 2 2: (x1{1} = sk_seed{2} ++ sk_prf{2} /\ size sk_seed{2} = 32 /\ size sk_prf{2} = 32 /\ size pub_seed{2} = 32).
             * outline {1} [1-2] { x1 <@ T.Program.Sample.sample(64); }.
               transitivity {1}  { x1 <@ T.SampleX.samplecat(32,32); }
               (true ==> ={x1})
               (true ==> x1{1} = sk_seed{2} ++ sk_prf{2} /\ size sk_seed{2} = 32 /\ size sk_prf{2} = 32 /\ size pub_seed{2} = 32) => //.
                 + by call sample_samplecat => //.
               inline*; auto; rewrite (: n = 32) //=. 
             * admit.
            * admit. 
(* TODO: FIXME: Add size = 32 to these *)
seq 0 0 : (#pre /\ size sk_seed{2} = 32 /\ size sk_prf{2} = 32 /\ size pub_seed{2} = 32); first by admit. (* FIXME This should be in the post of the previous seq *) 
(* TODO: FIXME: Add size = 32 to these *)
inline {1} M(Syscall).__xmssmt_core_seed_keypair. 
seq 12 0 : (#pre /\ pk0{1} = pk{1} /\  sk0{1} = sk{1} /\ seed0{1} = seed_p{1}); first by auto. 
seq 1 1 : (#pre /\ address{2} = top_tree_addr{1}).
    + (* exists * top_tree_addr{1}; elim * => _P; call {1} (zero_addr_op_impl _P). *) (* FIXME: TODO: This should work but I get a invalid goal shape *)
      inline {1}; wp; sp. 
      while {1} (0 <= i{1} <= 8 /\ forall (k : int), 0 <= k < i{1} => addr0{1}.[k] = W32.zero) (8 - i{1}).
         * auto => /> *; do split;1,2,4:smt(); move => k??; rewrite get_setE /#.
         * skip => /> *; split; [smt() |]; move => *; split; [smt() | move => ????; rewrite /zero_address; smt(@Array8)].
seq 1 1 : (#pre); first by inline {1}; auto => /> *; rewrite /set_layer_addr /#. 
seq 2 0 : (#pre /\ to_list idx{1} = nseq 4 W8.zero).
    + call {1} memset_nseq; auto. 
seq 1 0 : (
                 to_list seed_p{1} = sk_seed{2} ++ sk_prf{2} ++ pub_seed{2} /\
                 size sk_seed{2} = 32 /\ 
                 size sk_prf{2} = 32 /\ 
                 size pub_seed{2} = 32 /\
                 pk0{1} = pk{1} /\ 
                 seed0{1} = seed_p{1} /\
                 address{2} = top_tree_addr{1} /\
                 to_list idx{1} = nseq 4 W8.zero /\
                 forall (k : int), 0 <= k < 4 => sk0{1}.[k] = W8.zero
).
    + auto => /> &1 &2 ???? H. 
      have E : forall (k : int), 0 <= k < 4 => nth witness (to_list idx{1}) k = W8.zero by apply (nseq_nth (to_list idx{1}) 4 W8.zero);assumption.
      move => k??; rewrite initiE 1:/#; auto => />; rewrite ifT 1://=.
      rewrite -get_to_list; apply E => //.
seq 2 0 : (
  #pre /\
  forall (k : int), 0 <= k < 64 => buf1{1}.[k] = seed_p{1}.[k]
); first by auto => /> *; smt(@Array64).
seq 1 0 : (#pre /\ buf0{1} = buf1{1}); first by ecall {1} (_x_memcpy_u8u8_64_post buf1{1}); skip => />. 
seq 1 0 : (
  #pre /\ 
  forall (k : int), 0 <= k < 64 => sk0{1}.[4 + k] = seed0{1}.[k]
); first by auto => /> *; split; move => ???; rewrite initE ifT 1:/#; auto => />; [rewrite ifF /# | rewrite ifT /#]. 
seq 2 0 : (
  #pre /\
  forall (k : int), 0 <= k < 32 => bufn1{1}.[k] = seed_p{1}.[64 + k]
); first by auto => /> *; smt(@Array32).
seq 1 0 : (#pre /\ bufn0{1} = bufn1{1}); first by ecall {1} (_x_memcpy_u8u8_post bufn1{1}); skip => />. 
seq 1 0 : (
    #pre /\
    forall (k : int), 0 <= k < 32 => sk0{1}.[4 + 3 *32 + k] = seed_p{1}.[64 + k]
); first by auto => /> *; do split; move => *; rewrite initE ifT 1:/#; auto => />; [| | rewrite ifT /#]; rewrite ifF /#. 

(* -------------------------------------------------------------------------------------------------------------------------------- *)
(* Cleanup pre *)
seq 0 0 : (
  to_list seed_p{1} = sk_seed{2} ++ sk_prf{2} ++ pub_seed{2} /\
  size sk_seed{2} = 32 /\
  size sk_prf{2} = 32 /\
  size pub_seed{2} = 32 /\
  pk0{1} = pk{1} /\
  seed0{1} = seed_p{1} /\
  address{2} = top_tree_addr{1} /\
  to_list idx{1} = nseq 4 W8.zero /\
        

  (forall (k : int), 0 <= k <  4 => sk0{1}.[k] = W8.zero) /\ (* index *)
  (forall (k : int), 0 <= k < 64 => sk0{1}.[4 + k] = seed_p{1}.[k]) /\ (* sk seed & sk prf *)
  (forall (k : int), 0 <= k < 32 => sk0{1}.[4 + 3 * 32 + k] = seed_p{1}.[64 + k]) (* pub seed *)
); first by auto => />. 
(* -------------------------------------------------------------------------------------------------------------------------------- *)
seq 2 0 : (
  #pre /\
  (forall (k : int), 0 <= k < 32 => bufn1{1}.[k] = sk0{1}.[100 + k]) 
); first by auto => /> *; rewrite initiE /#. 
seq 1 0 : (#pre /\ bufn0{1} = bufn1{1}); first by ecall {1} (_x_memcpy_u8u8_post bufn1{1}); skip => />. 
seq 1 0 : (
  (* This is #pre but without the "pk0{1} = pk{1}" and the bufn parts *)
  to_list seed_p{1} = sk_seed{2} ++ sk_prf{2} ++ pub_seed{2} /\
  size sk_seed{2} = 32 /\
  size sk_prf{2} = 32 /\
  size pub_seed{2} = 32 /\
  seed0{1} = seed_p{1} /\
  address{2} = top_tree_addr{1} /\
  to_list idx{1} = nseq 4 W8.zero /\
  (forall (k : int), 0 <= k < 4 => sk0{1}.[k] = W8.zero) /\
  (forall (k : int), 0 <= k < 64 => sk0{1}.[4 + k] = seed_p{1}.[k]) /\
  (forall (k : int), 0 <= k < 32 => sk0{1}.[4 + 3 * 32 + k] = seed_p{1}.[64 + k]) /\

  (* this is new *)
  (forall (k : int), 0 <= k < 32 => pk0{1}.[32 + k] = sk0{1}.[100 + k])
); first by auto => &1 &2; move => [#] *; do split; 1..10: assumption; move => k?; rewrite initiE /#. 
seq 2 0 : (
  (* buf0 = sk seed /\ buf1 = pub seed *)
  #pre /\
  (forall (k : int), 0 <= k < 32 => bufn0{1}.[k] = sk0{1}.[4 + k]) /\
  (forall (k : int), 0 <= k < 32 => bufn1{1}.[k] = pk0{1}.[32 + k])
); first by auto => /> &1 &2 *; split => *; rewrite initiE //=.

seq 0 1 : (
  #pre /\
  toByte sk{2}.`idx 4 = sub sk0{1} 0  4  /\
  sk{2}.`sk_seed      = sub sk0{1} 4  32 /\
  sk{2}.`sk_prf       = sub sk0{1} 36 32 /\
  sk{2}.`pub_seed_sk  = sub sk0{1} 68 32  
).
    + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10; do split.
           - rewrite toByteZero. apply (eq_from_nth witness).
               * rewrite size_nseq size_sub /#.
             rewrite size_nseq (: max 0 4 = 4) //=  => i Hi.
             rewrite nth_nseq // nth_sub // /#.
           - apply (eq_from_nth witness); first by rewrite H1 size_sub //=.
             rewrite H1 => i Hi. 
             rewrite nth_sub //= H6 1:/# -get_to_list H0 nth_cat !size_cat H1 H2 ifT 1:/#.
             rewrite nth_cat H1 ifT 1:/# //=.
           - apply (eq_from_nth witness); first by rewrite H2 size_sub //=.
             rewrite H2 => i Hi. 
             rewrite nth_sub //=.  
             rewrite (nth_seed_1 (to_list seed_p{1}) sk_seed{2} sk_prf{2} pub_seed{2}) 1:/#.
             rewrite get_to_list /#. 
           - apply (eq_from_nth witness); first by rewrite H3 size_sub //=.
             rewrite H3 => i Hi.
             rewrite nth_sub 1:/#.
             rewrite (nth_seed_2 (to_list seed_p{1}) sk_seed{2} sk_prf{2} pub_seed{2}) 1:/#.
             rewrite get_to_list.  (* Isto esta certo mas a hipotese H7 devia ser falsa *)
             admit.
seq 1 1 : (#pre /\ root{2} = to_list root{1}).
    + admit.
admit.
qed.




(*** L Tree ***)

lemma ltree_correct (_pk : W8.t Array2144.t, _pub_seed : W8.t Array32.t, _addr : W32.t Array8.t) : 
    len = XMSS_WOTS_LEN /\ 
    n = XMSS_N =>
    equiv [
      M(Syscall).__l_tree ~ LTree.ltree :
      arg{1}.`2 = _pk /\
      arg{1}.`3 = _pub_seed /\
      arg{1}.`4 = _addr /\
      arg{2} = (EncodeWotsPk _pk, _addr, to_list _pub_seed)
      ==>
      to_list res{1}.`1 = res{2}.`1 /\ (* wots pk *)
      res{1}.`3 = res{2}.`2 (* address *)
    ].
proof.
move => [#] *.
proc. 
auto => />.
seq 3 1 : (#pre); first by auto. 
seq 1 1 : (#pre /\ _len{2} = to_uint l{1} /\ _len{2} = 67);  first by auto.
seq 2 1 : (
  addr{1} = address{2} /\
  pk{2} = EncodeWotsPk wots_pk{1} /\
  _seed{2} = to_list pub_seed{1} /\
  _len{2} = to_uint l{1} /\
  _len{2} = 67
); first by inline {1}; auto. 
seq 1 1 : (
  addr{1} = address{2} /\ 
  (forall (k : int), 0 <= k < 32 => wots_pk{1}.[k] = nth witness (nth witness pk{2} 0) k) /\
  size pk{2} = len /\
  forall (t : W8.t list), t \in pk{2} => size t = n
); last first.
    + ecall {1} (_x_memcpy_u8u8_post tmp{1}).
      auto => /> &1 &2 ???.
      apply (eq_from_nth witness); [ rewrite (size_nth pk{2} 32 0);1,2:smt(); by rewrite size_to_list | smt(@Array32) ].
(*-------------------------------------------------------------------------------------------------------------------------------------------*)
while (
  0 <= _len{2} <= 67 /\
  _len{2} = to_uint l{1} /\
  _seed{2} = to_list pub_seed{1} /\
  size pk{2} = len /\
  addr{1} = address{2} /\ 
  (forall (k : int), 0 <= k < 32 => wots_pk{1}.[k] = nth witness (nth witness pk{2} 0) k) /\
  (forall (t : W8.t list), t \in (pk{2}) => size t = n)
); last by admit.

    + seq 2 0 : (#pre /\ to_uint parent_nodes{1} = floor (len%r / 2%r)). 
      * auto => /> &1 &2 *. 
        have ->: truncateu8 (W256.one `&` (of_int 63)%W256) = W8.one by admit.
        rewrite shr_div.
        have ->: 2 ^ (to_uint W8.one %% 64) = 2 by smt(@W8).
        admit.
    
     

(* ------------------------- *)

    + skip => /> &1 *. do split.

smt().
smt().
rewrite size_enc_wots_pk /#.
move => k ? ?. 
    + admit. (* rewrite -nth_flatten. rewrite size_enc_wots_pk /#. rewrite (size_nth (EncodeWotsPk wots_pk{1}) 32 0); smt(size_enc_wots_pk ssize_enc_wots_pk). *)      
smt(ssize_enc_wots_pk).
smt(@W64 pow2_64).
smt(@W64 pow2_64).
qed.

(*** Treehash ***)

(******* exported functions ********)
