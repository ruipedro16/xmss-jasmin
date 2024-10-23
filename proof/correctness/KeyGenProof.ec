pragma Goals : printall.

require import AllCore List RealExp IntDiv Distr DList.
from Jasmin require import JModel JArray.

(* require import Types Params Parameters Address Notation Hash Primitives Wots XMSS_MT_PRF. *)
require import Params XMSS_MT_Params Types Address BaseW XMSS_MT_TreeHash XMSS_MT_PRF.
require import XMSS_IMPL Parameters.
require import Repr2 Utils2 DistrUtils.

require import Array3 Array8 Array32 Array64 Array68 Array96 Array131 Array352 Array2144.
require import WArray32 WArray96.

require import Correctness_Address Correctness_Mem Correctness_Hash.
require import TreehashProof.

require import BitEncoding.
(*---*) import BitChunking.

require import StdBigop. 
(*---*) import Bigint.

require import Termination.

clone import DListProgramX as T
  with type t <- W8.t,
       op d <- W8.dword.

lemma random_bytes_equiv :
    n = XMSS_N =>
    equiv [
      Syscall.randombytes_96 ~ XMSS_MT_PRF.sample_randomness :
      true 
      ==>
      to_list res{1} = val res{2}.`1 ++ val res{2}.`2 ++ val res{2}.`3
    ].    
proof.
rewrite /XMSS_N => n_val.
proc.
transitivity {2} { pub_seed <$ dlist W8.dword 96; }
(true ==> to_list a{1} = pub_seed{2})
(true ==> pub_seed{1} = (sk_seed{2} ++ sk_prf{2} ++ pub_seed{2}) /\ 
          size sk_seed{2} = n /\ size sk_prf{2} = n /\ size pub_seed{2} = n) => //.
  + auto => /> &1 &2  -> ???.
    congr; [congr |]; by rewrite insubdK // /P.

  + rnd Array96.to_list (Array96.of_list W8.zero): *0 *0.
    auto => />; split => [l | ?].

      * rewrite supp_dmap; move => [x].
        rewrite supp_dlist // => /> E _.
        by rewrite of_listK.
    split => [l | ?].
      * rewrite supp_dmap; move=> [x].
        rewrite darray_dlist dmap_comp /(\o) /=.
        rewrite supp_dlist //; move=> [[Ex Hx] ->].
        rewrite dmap_id dmap1E /(\o) /pred1 /=.
        apply mu_eq_support => y.
        rewrite supp_dlist //=; move=> [Ey Hy].
        rewrite eqboolP; split => //.
        move => E.
        by rewrite -(Array96.of_listK W8.zero y) // E of_listK.
    move => a; rewrite darray_dlist dmap_comp supp_dmap.
    move => [l]; rewrite supp_dlist // => [[[Esz] H]].
    rewrite /(\o) /= => ->.
    by rewrite of_listK // dmap_id // supp_dlist //.
(* At this point, we are no longer dealing with WArrays, we are only reasoning about lists *)
(* We have the same distribution on both sides, the only difference is that on the left side we
   generate 3*n = 96 bytes at once, and on the right side we generate n = 32 bytes three times.
   At this point, we can use the results from DListUtils.ec to prove that these are equivalent *) 

outline {1} [1] { pub_seed <@ T.Program.Sample.sample(96); }.
transitivity {1}
 { pub_seed <@ T.SampleX.samplecat(64,32); }
 (true ==> ={pub_seed})
 (true ==> pub_seed{1} = sk_seed{2} ++ sk_prf{2} ++ pub_seed{2} /\  
           size sk_seed{2} = n /\ size sk_prf{2} = n /\ size pub_seed{2} = n) => //.
   + by call sample_samplecat.

inline.
swap {1} 2 1.
seq 2 2: (
   x1{1} = sk_seed{2} ++ sk_prf{2} /\ 
   size sk_seed{2} = n /\ size sk_prf{2} = n
); last by auto => /> *; smt(@DList).


outline {1} [1-2] { x1 <@ T.Program.Sample.sample(64); }.

transitivity {1}
{ x1 <@ T.SampleX.samplecat(32,32); }
(true ==> ={x1})
(true ==> x1{1} = sk_seed{2} ++ sk_prf{2} /\ size sk_seed{2} = n /\ size sk_prf{2} = n) => //.
  + by call sample_samplecat.
  + inline.
    auto => /> *.  
    smt(@DList).
qed.


(*** Keygen without OID ***)
lemma xmss_kg_no_oid : 
    n = XMSS_N /\ 
    d = XMSS_D /\
    h = XMSS_TREE_HEIGHT =>
    equiv [
      M(Syscall).__xmssmt_core_keypair ~ XMSS_MT_PRF.kg :
      true 
      ==>
      res{1}.`1 = DecodePkNoOID res{2}.`2 /\
      res{1}.`2 = DecodeSkNoOID res{2}.`1
    ].
proof.
rewrite /XMSS_N /XMSS_D => [#] n_val d_val h_val. 
proc => /=. 
sp 3 4.
seq 1 1 : (
  address{2} = set_layer_addr zero_address (d - 1) /\ 
  to_list seed_p{1} = val sk_seed{2} ++ val sk_prf{2} ++ val pub_seed{2}
); first by call random_bytes_equiv. 

inline {1} M(Syscall).__xmssmt_core_seed_keypair. 
sp 10 0.
  
conseq (:
  pk0{1} = pk{1} /\
  sk0{1} = sk{1} /\
  seed0{1} = seed_p{1} /\
  address{2} = set_layer_addr zero_address (d - 1) /\
  to_list seed_p{1} = val sk_seed{2} ++ val sk_prf{2} ++ val pub_seed{2} /\
  val sk_seed{2}  = sub seed_p{1} 0 n /\
  val sk_prf{2}   = sub seed_p{1} n n /\
  val pub_seed{2} = sub seed_p{1} (2*n) n
  ==>
  _
).
    + auto => /> &1 &2 H; do split.
           * apply (eq_from_nth witness); first by rewrite valP size_sub n_val.
             rewrite valP n_val => i?.
             rewrite nth_sub // -get_to_list H nth_cat ifT; [by rewrite size_cat !valP n_val /= /# |].
             rewrite nth_cat ifT // valP n_val /#. 
           * apply (eq_from_nth witness); first by rewrite valP size_sub n_val.
             rewrite valP n_val => i?.
             rewrite nth_sub // -get_to_list H nth_cat ifT; [by rewrite size_cat !valP n_val /= /# |].
             rewrite nth_cat ifF // valP n_val /#. 
           * apply (eq_from_nth witness); first by rewrite valP size_sub n_val.
             rewrite valP n_val => i?.
             rewrite nth_sub // -get_to_list H nth_cat ifF; [by rewrite size_cat !valP n_val /= /# |].
             by rewrite size_cat !valP n_val.

seq 2 0 : (
    #{/~address{2} = set_layer_addr zero_address (d - 1)}pre /\
    address{2} = top_tree_addr{1}
).
    + inline {1} 2; wp.
      inline {1} 1; wp; sp.
      exists * top_tree_addr{1}; elim * => _P. 
      call {1} (zero_addr_res _P). (* NOTE: This requires zero_addr to be phoare because on the right hand side we have an operator and on the left hand side we have a procedure call *)
      skip => /> &1 &2 *.
      by rewrite /set_layer_addr d_val /=.

seq 2 0 : (#pre /\ to_list idx{1} = nseq XMSS_INDEX_BYTES W8.zero); first by call {1} memset_nseq; auto. 

seq 1 0 : (#{/~sk0{1} = sk{1}}pre /\ (forall (k : int), 0 <= k < XMSS_INDEX_BYTES => sk0{1}.[k] = W8.zero)).
    + auto => /> &1 &2 *. 
      rewrite initE ifT 1:/# => />. 
      have E : forall (k : int), 0 <= k < XMSS_INDEX_BYTES => nth witness (to_list idx{1}) k = W8.zero.
           * by apply (nseq_nth (to_list idx{1}) XMSS_INDEX_BYTES W8.zero) ; assumption.
      by rewrite ifT // -get_to_list E. 

seq 2 0 : (#pre /\ (forall (k : int), 0 <= k < 64 => buf1{1}.[k] = seed_p{1}.[k])); first by auto => /> *; rewrite initiE.
seq 1 0 : (#pre /\ buf0{1} = buf1{1}); first by ecall {1} (_x_memcpy_u8u8_64_post buf1{1}); skip => />. 

seq 1 0 : (
  #{/~forall (k : int), 0 <= k && k < 64 => buf1{1}.[k] = seed_p{1}.[k]}
   {/~buf0{1} = buf1{1}}pre /\
   (forall (k : int), 0 <= k < 32 => sk0{1}.[XMSS_INDEX_BYTES + k] = nth witness (val sk_seed{2}) k) /\
   (forall (k : int), 0 <= k < 32 => sk0{1}.[XMSS_INDEX_BYTES + n + k] = nth witness (val sk_prf{2}) k)
).
    + auto => /> &1 &2 ?H0 H1 ??? H2; do split => *.
        * rewrite initiE 1:/#; auto => />; rewrite ifF /#.
        * by rewrite initiE 1:/#; auto => />; rewrite ifT 1:/# H2 1:/# H0 n_val nth_sub. 
        * by rewrite initiE 1:/#; auto => />; rewrite ifT 1:/# H2 1:/# H1 n_val nth_sub.
 
seq 2 0 : (#pre /\ (forall (k : int), 0 <= k < 32 => bufn1{1}.[k] = seed_p{1}.[64 + k])); first by auto => /> *; rewrite initiE.
seq 1 0 : (#pre /\ bufn0{1} = bufn1{1}); first by ecall {1} (_x_memcpy_u8u8_post bufn1{1}); skip => />.
 
seq 2 0 : (
  #{/~forall (k : int), 0 <= k && k < 32 => bufn1{1}.[k] = seed_p{1}.[64 + k]}
   {/~bufn0{1} = bufn1{1}}pre /\
   (forall (k : int), 0 <= k < n => sk0{1}.[XMSS_INDEX_BYTES + 3 * n + k] = nth witness (val pub_seed{2}) k)
).
    + auto => /> &1 &2 ???->????H. 
    (* A seta refere-se a hipotese val pub_seed{2} = sub seed_p{1} (2 * n) n *)
      do split => *; rewrite initiE 1:/#; auto => />; first by smt().
        * by rewrite ifF /#.  
        * by rewrite ifF /#.
        * rewrite ifT 1:/# //= H 1:/# /XMSS_INDEX_BYTES n_val nth_sub /#. 

seq 1 0 : (#pre /\ (forall (k : int), 0 <= k < 32 => bufn1{1}.[k] = sk0{1}.[XMSS_INDEX_BYTES + 3 * 32 + k])); first by auto => /> *; rewrite initiE. 
seq 1 0 : (#pre /\ bufn0{1} = bufn1{1}); first by ecall {1} (_x_memcpy_u8u8_post bufn1{1}); skip => />. 
 
seq 1 0 : (
  #{/~forall (k : int), 0 <= k && k < 32 => bufn1{1}.[k] = sk0{1}.[100 + k]}
   {/~bufn0{1} = bufn1{1}}
   {/~pk0{1} = pk{1}}pre /\
   (forall (k : int), 0 <= k < 32 => pk0{1}.[32 + k] = nth witness (val pub_seed{2}) k)
). 
    + auto => /> &1 &2 ???->???? H0 H1 => *.
      (* A seta refere se a hipotese val pub_seed{2} = sub seed_p{1} (2 * n) n *)
      rewrite n_val /= in H0.
      by rewrite initiE 1:/# nth_sub 1:/# n_val /= ifT 1:/# H1 // H0 // nth_sub 1:/#.

seq 2 0 : (
  #pre /\
  to_list bufn0{1} = val sk_seed{2} /\
  to_list bufn1{1} = val pub_seed{2}
).
    + auto => /> &1 &2 ?????? H0 ? H1 ? H2.
      rewrite n_val /= in H1.
      do split.
        - move => k??.
          by rewrite initiE //= H2 // H1.
        - apply (eq_from_nth witness); [by rewrite valP size_to_list n_val |].
          rewrite size_to_list => i?.
          by rewrite get_to_list initiE 1:/# /= -H0.
        - apply (eq_from_nth witness); [by rewrite valP size_to_list n_val |].
          rewrite size_to_list => i?.
          by rewrite get_to_list initiE 1:/# /= H2 // H1.
 
seq 0 1 : (
    #pre /\ 
    toByte sk{2}.`idx XMSS_INDEX_BYTES = sub sk0{1} 0  XMSS_INDEX_BYTES  /\ 
    val sk{2}.`sk_seed                 = sub sk0{1} XMSS_INDEX_BYTES n /\
    val sk{2}.`sk_prf                  = sub sk0{1} (XMSS_INDEX_BYTES + n) n /\
    val sk{2}.`pub_seed_sk             = sub sk0{1} (XMSS_INDEX_BYTES + 3*n) n 
    (* NOTA: a pub seed e a root estao trocadas => Na spec a root vem no fim mas na impl no fim esta a pub seed => a root esta entre a sk prf e a pub seed *)
).

    + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12; do split.
      * apply (eq_from_nth witness); rewrite /toByte size_take //= size_rev size_to_list //=; [ by rewrite size_sub //= |] => i?. 
        rewrite nth_sub //= nth_take //= 1:/# nth_rev 1:#smt:(size_to_list) size_to_list //=.
        have ->: to_list (unpack8 W32.zero) = nseq 4 W8.zero.
             - apply (eq_from_nth W8.zero); [ by rewrite size_to_list size_nseq |].
               rewrite size_to_list => j?.
               rewrite get_to_list nth_nseq //= get_unpack8 //= get_zero //.
        by rewrite nth_nseq 1:/# H5 1:/#.
      * apply (eq_from_nth witness); first by rewrite valP n_val size_sub //.
        rewrite valP n_val => ??.
        by rewrite -H6 // nth_sub.
      * apply (eq_from_nth witness); first by rewrite valP n_val size_sub //.   
        rewrite valP n_val => ??.
        by rewrite -H7 // nth_sub // /XMSS_INDEX_BYTES n_val. 
      * apply (eq_from_nth witness); first by rewrite valP n_val size_sub //.   
        rewrite valP n_val => ??.
        rewrite n_val in H8.
        by rewrite nth_sub //= H8.
        
seq 1 1 : (#pre /\ val root{2} = to_list root{1}).
    + inline M(Syscall).__treehash_ M(Syscall)._treehash.
      sp.
      exists * sk_seed0{1}, pub_seed0{1}, s0{1}, t0{1}, subtree_addr0{1}.
      elim * => P0 P1 P2 P3 P4.
      wp; sp.
      call {1} (treehash_correct P0 P1 P2 P3 P4) => [/# |].
      simplify.

      auto => /> &1 &2 ??????????? -> -> *.
(* Neste auto, as setas referem se as hipoteses to_list P0 = val sk_seed{2} =>
to_list P1 = val pub_seed{2} =>
*)
      do split; [| | by move => ?????? ->]; by smt(@NBytes).

seq 1 0  : ( 
  #pre /\
  (forall (k : int), 0 <= k < n => pk0{1}.[k] = nth witness (val root{2}) k)
).
    + exists * pk0{1}, root{1}.
      elim * => P0 P1.
      call {1} (nbytes_copy_64_32_p P0 P1). (* We need the phoare version of the lemma here *)
      skip => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 result H18 H19.
      have E : forall (k : int), 0 <= k < 32 => nth witness (sub result 32 32) k = nth witness (sub P0 32 32) k by smt().
      rewrite n_val; split => k??. 
     
        * rewrite -H10 //.
          have ->: result.[32 + k] = nth witness (sub result 32 32) k by rewrite nth_sub.
          by rewrite E // nth_sub.
        * by rewrite H17 -H18 nth_sub. 
   
seq 1 0 : (
  #pre /\
  (forall (k : int), 0 <= k < 32 => sk0{1}.[XMSS_INDEX_BYTES + 2 * 32 + k] = nth witness (val root{2}) k)
).

    + exists * sk0{1}, root{1}; elim * => P0 P1. 
      call {1} (nbytes_copy_131_32_p P0 P1). (* Here, we need the phoare version of the lemma *)
      skip => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 result  H19 H20 H21*.
      have E0: forall (k : int), 0 <= k < 67 => nth witness (sub result 0 67) k = nth witness (sub P0 0 67) k by smt().
      do split.
        * move => k??.
          have ->: result.[k] = nth witness (sub result 0 67) k by rewrite nth_sub 1:/#.          
          by rewrite E0 1:/# nth_sub 1:/# /= H5.
        * move => k??.
          have ->: result.[XMSS_INDEX_BYTES + k] = nth witness (sub result 0 67) (XMSS_INDEX_BYTES + k) by rewrite nth_sub 1:/#.          
          by rewrite H20 nth_sub 1:/# /= H6. 
        * move => k??.
          have ->: result.[XMSS_INDEX_BYTES + n + k] = nth witness (sub result 0 67) (XMSS_INDEX_BYTES + n + k) by rewrite nth_sub 1:/#.          
          by rewrite H20 nth_sub 1:/# /= H7. 
        * move => k??.
          rewrite -H8 //.
          have ->: result.[XMSS_INDEX_BYTES + 3 * n + k] = nth witness (sub result 99 32) k by rewrite nth_sub // /#.
          by rewrite H21 nth_sub 1:/# /XMSS_INDEX_BYTES n_val /=. 
        * move => k??.
          rewrite H9 //.
          have ->: result.[XMSS_INDEX_BYTES + 96 + k] = nth witness (sub result 99 32) k by rewrite nth_sub // /#.
          by rewrite H21 nth_sub.
        * rewrite H13.
          apply (sub_sub_minus P0 result XMSS_INDEX_BYTES 67) => //. 
          by rewrite H20.
        * rewrite H14.
          apply (eq_from_nth witness); first by rewrite !size_sub // /#.
          rewrite size_sub 1:/# n_val => j?.
          rewrite !nth_sub //. 
          have ->: result.[XMSS_INDEX_BYTES + j] = nth witness (sub result 0 67) (XMSS_INDEX_BYTES + j) by rewrite nth_sub 1:/#.          
          by rewrite H20 nth_sub 1:/# /=. 
        * rewrite H15.
          apply (eq_from_nth witness); first by rewrite !size_sub /#.
          rewrite size_sub 1:/# n_val => j?.
          rewrite !nth_sub //.
          have ->: P0.[XMSS_INDEX_BYTES + 32 + j] = nth witness (sub P0 0 67) (XMSS_INDEX_BYTES + 32 + j) by rewrite nth_sub /#.
          by rewrite -H20 nth_sub /#.
        * rewrite H16.
          apply (eq_from_nth witness); first by rewrite !size_sub /#.
          rewrite size_sub 1:/# n_val => j?.
          rewrite !nth_sub //.
          have ->: result.[XMSS_INDEX_BYTES + 3 * 32 + j] = nth witness (sub result 99 32) j by rewrite nth_sub // /#.
          by rewrite H21 nth_sub.
        * move => k??. 
          by rewrite H17 -H19 nth_sub.

(* ============================================================================================================================== *)

auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19; split.
    + rewrite /DecodePkNoOID => />; rewrite tP => i Hi.
      rewrite get_of_list //=.
      case (0 <= i < 32).
        + move => ?.
          by rewrite nth_cat valP n_val ifT 1:/# H18 // n_val.  
        + move => ?. 
          rewrite nth_cat valP n_val ifF 1:/# -H10 // 1:/#.
    + rewrite /DecodeSkNoOID => />; rewrite tP => i Hi. 
      rewrite -!get_to_list.
      case (0 <= i < XMSS_INDEX_BYTES).
        + move => ?. 
          rewrite of_listK; first by rewrite !size_cat !valP n_val size_take // ifT 2:/# size_W32toBytes.
          rewrite nth_cat !size_cat !valP n_val size_take // size_W32toBytes /= ifT 1:/#.
          rewrite nth_cat !size_cat size_take // !valP n_val /= ifT; [by rewrite ifT 2:/# size_W32toBytes /# |].
          rewrite nth_cat ifT.
             * rewrite size_cat size_take // ifT; [by rewrite size_W32toBytes | rewrite valP /#].
          rewrite nth_cat ifT; [by rewrite size_take 1:/# ifT 2:/# size_W32toBytes |].
          rewrite nth_take 1,2:/# W32toBytes_zero_nth 1:/#.
          by apply H5.

     case (XMSS_INDEX_BYTES <= i < XMSS_INDEX_BYTES + n).
        + simplify => ? _. 
          rewrite get_of_list //=.
          rewrite nth_cat !size_cat !valP n_val /= ifT.
             * rewrite size_take // size_W32toBytes ifT // /#.
          rewrite nth_cat ifT.
             * rewrite !size_cat !valP n_val /= size_take // size_W32toBytes /#.
          rewrite nth_cat ifT.
             * rewrite !size_cat !valP n_val /= size_take // size_W32toBytes /#.
          rewrite nth_cat ifF.
             * rewrite size_take // size_W32toBytes /#. 
          rewrite size_take // size_W32toBytes ifT 1:/#.
          rewrite -H6 /#.

      case (XMSS_INDEX_BYTES + n <= i < XMSS_INDEX_BYTES + 2 * n).
        + simplify => ? _ _.
          rewrite get_of_list //=.
          rewrite nth_cat !size_cat ifT.
             * rewrite !valP n_val /= size_take // size_W32toBytes /#.
          rewrite nth_cat !size_cat ifT.
             * rewrite !valP n_val /= size_take // size_W32toBytes /#.
          rewrite nth_cat !size_cat ifF.
             * rewrite !valP n_val /= size_take // size_W32toBytes /#.
          rewrite valP size_take // size_W32toBytes ifT 1:/#.
          rewrite -H7 /#.

      case (XMSS_INDEX_BYTES + 2*n <= i < XMSS_INDEX_BYTES + 3*n).
        + simplify => ? _ _ _.
          rewrite get_of_list //=.
          rewrite nth_cat !size_cat ifT.
            * rewrite !valP n_val /= size_take 1:/# size_W32toBytes /#.
          rewrite nth_cat !size_cat ifF.
            * rewrite !valP n_val /= size_take 1:/# size_W32toBytes /#.
          rewrite !valP n_val size_take 1:/# size_W32toBytes ifT 1:/#.
          rewrite -H18 /#.

      move => ????.      
      rewrite get_to_list of_listK.
            * rewrite !size_cat !valP n_val /= size_take // size_W32toBytes /#.  
      rewrite nth_cat !size_cat !valP n_val size_take // size_W32toBytes /#.
qed.

