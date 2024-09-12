pragma Goals : printall.

require import AllCore List RealExp IntDiv Distr DList.
from Jasmin require import JModel JArray.

require import Types Params Parameters Address Notation Hash Primitives Wots XMSS_MT_PRF.
require import XMSS_IMPL.
require import Repr. 
require import Utils.

require import Array4 Array8 Array32 Array64 Array68 Array96 Array132 Array136 Array352 Array2144.
require import WArray32 WArray96 WArray136.

require import Correctness_Address Correctness_Mem Correctness_Hash.
require import Utils DistrUtils.

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
      to_list res{1} = res{2}.`1 ++ res{2}.`2 ++ res{2}.`3
    ].    
proof.
rewrite /XMSS_N => n_val.
proc.
transitivity {2} { pub_seed <$ dlist W8.dword 96; }
(true ==> to_list a{1} = pub_seed{2})
(true ==> pub_seed{1} = (sk_seed{2} ++ sk_prf{2} ++ pub_seed{2}) ) => //.
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
    by rewrite of_listK //= dmap_id supp_dlist //.
(* At this point, we are no longer dealing with WArrays, we are only reasoning about lists *)
(* We have the same distribution on both sides, the only difference is that on the left side we
   generate 3*n = 96 bytes at once, and on the right side we generate n = 32 bytes three times.
   At this point, we can use the results from DListUtils.ec to prove that these are equivalent *) 
outline {1} [1] { pub_seed <@ T.Program.Sample.sample(96); }.
transitivity {1}
 { pub_seed <@ T.SampleX.samplecat(64,32); }
 (true ==> ={pub_seed})
 (true ==> pub_seed{1} = sk_seed{2} ++ sk_prf{2} ++ pub_seed{2}) => //; first by call sample_samplecat => //.
inline*; swap {1} 2 1.
seq 2 2: (x1{1} = sk_seed{2} ++ sk_prf{2}).
   + outline {1} [1-2] { x1 <@ T.Program.Sample.sample(64); }.
     transitivity {1}
     { x1 <@ T.SampleX.samplecat(32,32); }
     (true ==> ={x1})
     (true ==> x1{1} = sk_seed{2} ++ sk_prf{2}) => //.
        * by call sample_samplecat => //.
     by inline*; auto; rewrite n_val. 
by auto; rewrite n_val.
qed.

(* Same as randombytes_equiv but the spec is on the lhs and the impl is on the rhs *)
(* In random_bytes_results conseq only works with the spec is on the lhs *)
lemma random_bytes_equiv_flipped :
    n = XMSS_N =>
    equiv [XMSS_MT_PRF.sample_randomness ~ Syscall.randombytes_96  :
      true ==> to_list res{2} = res{1}.`1 ++ res{1}.`2 ++ res{1}.`3]
        by move => ?; symmetry; apply random_bytes_equiv => //=.

lemma random_bytes_results :
    n = XMSS_N =>
    equiv [
      Syscall.randombytes_96 ~ XMSS_MT_PRF.sample_randomness :
      true 
      ==>
      to_list res{1} = res{2}.`1 ++ res{2}.`2 ++ res{2}.`3 /\
      size res{2}.`1 = n /\
      size res{2}.`2 = n /\
      size res{2}.`3 = n 
    ].    
proof.
move => nP.
symmetry. 
conseq (random_bytes_equiv_flipped nP) sample_randomness_size.
qed.

(*** Keygen without OID ***)
lemma xmss_kg_no_oid : 
    n = XMSS_N /\ 
    d = XMSS_D =>
    equiv [
      M(Syscall).__xmssmt_core_keypair ~ XMSS_MT_PRF.kg :
      true 
      ==>
      res{1}.`1 = DecodePkNoOID res{2}.`2 /\
      res{1}.`2 = DecodeSkNoOID res{2}.`1
    ].
proof.
rewrite /XMSS_N /XMSS_D => [#] *. 
proc. 
seq 3 6 : (true); first by auto. 
swap {2} 3 -2. 
seq 1 1 : (
  to_list seed_p{1} = sk_seed{2} ++ sk_prf{2} ++ pub_seed{2} /\
  size sk_seed{2} = 32 /\
  size sk_prf{2} = 32 /\
  size pub_seed{2} = 32 
); first by call random_bytes_results => //=; skip => /> /#.
inline {1} M(Syscall).__xmssmt_core_seed_keypair. 
seq 12 0 : (#pre /\ pk0{1} = pk{1} /\  sk0{1} = sk{1} /\ seed0{1} = seed_p{1}); first by auto. 
seq 0 0 : (
  #pre /\
  (forall (k : int), 0 <= k < 32 => seed_p{1}.[k] = nth witness sk_seed{2} k) /\
  (forall (k : int), 0 <= k < 32 => seed_p{1}.[32+k] = nth witness sk_prf{2} k) /\
  (forall (k : int), 0 <= k < 32 => seed_p{1}.[64+k] = nth witness pub_seed{2} k)
).
    + auto => /> &1 &2 H0 H1 H2 H3; do split => k??. 
        * rewrite -get_to_list H0 nth_cat !size_cat H1 H2 ifT 1:/# nth_cat H1 ifT //=.
        * rewrite -get_to_list H0 nth_cat !size_cat H1 H2 ifT 1:/# nth_cat H1 ifF /#.
        * rewrite -get_to_list H0 nth_cat !size_cat H1 H2 ifF /#.  
seq 1 1 : (#pre /\ address{2} = top_tree_addr{1}).
    + inline M(Syscall).__zero_address_; wp; sp.
      exists * top_tree_addr{1}; elim * => _P. 
      call {1} (zero_addr_res _P); auto. (* NOTE: This requires zero_addr to be phoare because on the right hand side we have an operator and on the left hand side we have a procedure call *)
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
  (forall (k : int), 0 <= k < 4 => sk0{1}.[k] = W8.zero) /\
  (forall (k : int), 0 <= k < 32 => seed_p{1}.[k] = nth witness sk_seed{2} k) /\
  (forall (k : int), 0 <= k < 32 => seed_p{1}.[32+k] = nth witness sk_prf{2} k) /\
  (forall (k : int), 0 <= k < 32 => seed_p{1}.[64+k] = nth witness pub_seed{2} k)
).
    + auto => /> &1 &2 ???? H???. 
      have E : forall (k : int), 0 <= k < 4 => nth witness (to_list idx{1}) k = W8.zero by apply (nseq_nth (to_list idx{1}) 4 W8.zero); assumption.
      move => k??; rewrite initiE 1:/#; auto => />; rewrite ifT 1://=.
      rewrite -get_to_list; apply E => //.
seq 2 0 : (
  #pre /\
  forall (k : int), 0 <= k < 64 => buf1{1}.[k] = seed_p{1}.[k]
); first by auto => /> *; smt(@Array64).
seq 1 0 : (#pre /\ buf0{1} = buf1{1}); first by ecall {1} (_x_memcpy_u8u8_64_post buf1{1}); skip => />. 

seq 1 0 : (
  to_list seed_p{1} = sk_seed{2} ++ sk_prf{2} ++ pub_seed{2} /\
  size sk_seed{2} = 32 /\
  size sk_prf{2} = 32 /\
  size pub_seed{2} = 32 /\
  pk0{1} = pk{1} /\
  seed0{1} = seed_p{1} /\
  address{2} = top_tree_addr{1} /\

  (forall (k : int), 0 <= k < 32 => seed_p{1}.[k] = nth witness sk_seed{2} k) /\
  (forall (k : int), 0 <= k < 32 => seed_p{1}.[32 + k] = nth witness sk_prf{2} k) /\
  (forall (k : int), 0 <= k < 32 => seed_p{1}.[64 + k] = nth witness pub_seed{2} k) /\

  to_list idx{1} = nseq 4 W8.zero /\

  (forall (k : int), 0 <= k < 4 => sk0{1}.[k] = W8.zero) /\
  (forall (k : int), 0 <= k < 32 => sk0{1}.[4 + k] = nth witness sk_seed{2} k) /\
  (forall (k : int), 0 <= k < 32 => sk0{1}.[4 + 32 + k] = nth witness sk_prf{2} k)
).
    + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9; do split => k ??.
        * rewrite initiE 1:/#; auto => />; rewrite ifF 1:/#; apply H5 => //.
        * rewrite initiE 1:/#; auto => />; rewrite ifT 1:/# H9 1:/#; apply H6 => //.
        * rewrite initiE 1:/#; auto => />; rewrite ifT 1:/# H9 1:/#; apply H7 => //.

seq 2 0 : (
  #pre /\
  forall (k : int), 0 <= k < 32 => bufn1{1}.[k] = seed_p{1}.[64 + k]
); first by auto => /> *; smt(@Array32).
seq 1 0 : (#pre /\ bufn0{1} = bufn1{1}); first by ecall {1} (_x_memcpy_u8u8_post bufn1{1}); skip => />. 
seq 1 0 : (
  to_list seed_p{1} = sk_seed{2} ++ sk_prf{2} ++ pub_seed{2} /\
  size sk_seed{2} = 32 /\
  size sk_prf{2} = 32 /\
  size pub_seed{2} = 32 /\
  pk0{1} = pk{1} /\
  seed0{1} = seed_p{1} /\
  address{2} = top_tree_addr{1} /\

  (forall (k : int), 0 <= k < 32 => seed_p{1}.[k] = nth witness sk_seed{2} k) /\
  (forall (k : int), 0 <= k < 32 => seed_p{1}.[32 + k] = nth witness sk_prf{2} k) /\
  (forall (k : int), 0 <= k < 32 => seed_p{1}.[64 + k] = nth witness pub_seed{2} k) /\

  to_list idx{1} = nseq 4 W8.zero /\

  (forall (k : int), 0 <= k < 4 => sk0{1}.[k] = W8.zero) /\
  (forall (k : int), 0 <= k < 32 => sk0{1}.[4 + k] = nth witness sk_seed{2} k) /\
  (forall (k : int), 0 <= k < 32 => sk0{1}.[4 + 32 + k] = nth witness sk_prf{2} k) /\
  (forall (k : int), 0 <= k < 32 => sk0{1}.[4 + 3 * 32 + k] = nth witness pub_seed{2} k)
).
    + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11; do split => k??; rewrite initiE 1:/#; auto => />; first by smt(). 
       * rewrite ifF 1:/# -H9 //=.  
       * rewrite ifF 1:/# -H10 //=.
       * rewrite ifT 1:/# -H6 //= H11 //=. 

(* At this point, sk has all the fields set (except for the root) *)

seq 2 0 : (
  #pre /\
  (forall (k : int), 0 <= k < 32 => bufn1{1}.[k] = sk0{1}.[100 + k]) 
); first by auto => /> *; rewrite initiE /#. 
seq 1 0 : (#pre /\ bufn0{1} = bufn1{1}); first by ecall {1} (_x_memcpy_u8u8_post bufn1{1}); skip => />. 

seq 1 0 : (
  to_list seed_p{1} = sk_seed{2} ++ sk_prf{2} ++ pub_seed{2} /\
  size sk_seed{2} = 32 /\
  size sk_prf{2} = 32 /\
  size pub_seed{2} = 32 /\
  seed0{1} = seed_p{1} /\
  address{2} = top_tree_addr{1} /\

  (forall (k : int), 0 <= k < 32 => seed_p{1}.[k] = nth witness sk_seed{2} k) /\
  (forall (k : int), 0 <= k < 32 => seed_p{1}.[32 + k] = nth witness sk_prf{2} k) /\
  (forall (k : int), 0 <= k < 32 => seed_p{1}.[64 + k] = nth witness pub_seed{2} k) /\

  to_list idx{1} = nseq 4 W8.zero /\


  (forall (k : int), 0 <= k < 4 => sk0{1}.[k] = W8.zero) /\
  (forall (k : int), 0 <= k < 32 => sk0{1}.[4 + k] = nth witness sk_seed{2} k) /\
  (forall (k : int), 0 <= k < 32 => sk0{1}.[4 + 32 + k] = nth witness sk_prf{2} k) /\
  (forall (k : int), 0 <= k < 32 => sk0{1}.[4 + 3 * 32 + k] = nth witness pub_seed{2} k) /\

  (forall (k : int), 0 <= k < 32 => pk0{1}.[32 + k] = nth witness pub_seed{2} k) (* this is the pub seed *)
).
    + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 k ??.
      rewrite initE ifT 1:/#; auto => />.
      rewrite ifT 1:/# -H11 1:/# H12 //=.  

seq 2 0 : (
  #pre /\
  to_list bufn0{1} = sk_seed{2} /\
  to_list bufn1{1} = pub_seed{2}
).
    + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12; split. 
        - apply (eq_from_nth witness); [by rewrite size_to_list H1 | rewrite size_to_list => i?].
          rewrite get_to_list initiE 1:/#; auto => />; rewrite -H9 //=.
        - apply (eq_from_nth witness); [by rewrite size_to_list H3 | rewrite size_to_list => i?].
          rewrite get_to_list initiE 1:/#; auto => />; rewrite H12 1:/# //=.

seq 0 1 : (
    #pre /\ 
    toByte sk{2}.`idx 4 = sub sk0{1} 0  4  /\
    sk{2}.`sk_seed      = sub sk0{1} 4  32 /\
    sk{2}.`sk_prf       = sub sk0{1} 36 32 /\
    sk{2}.`pub_seed_sk  = sub sk0{1} 100 32 (* NOTA: a pub seed e a root estao trocadas => Na spec a root vem no fim mas na impl no fim esta a pub seed => a root esta entre a sk prf e a pub seed *)
).

    + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12; do split.
      * apply (eq_from_nth witness); rewrite /toByte size_take //= size_rev size_to_list //=; [ by rewrite size_sub //= |] => i?. 
        rewrite nth_sub //= nth_take //= 1:/# nth_rev 1:#smt:(size_to_list) size_to_list //=.
        have ->: to_list (unpack8 W32.zero) = nseq 4 W8.zero.
             - apply (eq_from_nth W8.zero); [ by rewrite size_to_list size_nseq |].
               rewrite size_to_list => j?.
               rewrite get_to_list nth_nseq //= get_unpack8 //= get_zero //.
        rewrite nth_nseq 1:/# H8 //=.    
      * apply (eq_from_nth witness); [by rewrite size_to_list size_sub | rewrite size_to_list] => i?.
        rewrite get_to_list nth_sub //= H9 //.
      * apply (eq_from_nth witness); [by rewrite H2 size_sub | rewrite H2] => i?.
        rewrite nth_sub //= H10 //.
      * apply (eq_from_nth witness); [by rewrite size_to_list size_sub | rewrite size_to_list] => i?.
        rewrite nth_sub //= -H11 //=.

seq 1 1 : (#pre /\ root{2} = to_list root{1}).
    + admit. (* call to treehash lemma *)

seq 1 0  : ( 
  #pre /\
  (forall (k : int), 0 <= k < 32 => pk0{1}.[k] = nth witness root{2} k)
).
    + inline {1}. wp.
      while {1}  
      (
        #pre /\  
        0 <= i{1} <= 32 /\ 
        offset_out{1} = W64.zero /\
        offset_in{1} = W64.zero /\
        in_0{1} = root{1} /\
        out{1} = pk0{1} /\
        (forall (k : int), 0 <= k < i{1} => out{1}.[k] = root{1}.[k])
      ) 
      (32 - i{1}); last first. (* FIXME: TODO: Remover lemmas de pk0 da #pre *)
        - auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 *; split => [/# | iL];  split => [/# | ???]. 
          have ->: iL = 32 by smt(). 
          move => H17 /#. 
        - auto => /> &hr *; do split; 1,2,5:smt(). 
             * rewrite tP => *; admit.
             * move => k??; rewrite get_setE; [by split; by rewrite of_uintK /# |]. 
               rewrite of_uintK (: i{hr} %% W64.modulus = i{hr}) /#.  

seq 1 0 : (
  #pre /\
  (forall (k : int), 0 <= k < 32 => sk0{1}.[4 + 2 * 32 + k] = nth witness root{2} k)
). 
    + inline {1}.  wp.
      while {1} 
      (
        #pre /\ 
        0 <= i{1} <= 32 /\ 
        offset_in{1} = W64.zero /\
        to_uint offset_out{1} = 68 /\
        out{1} = sk0{1} /\
        in_0{1} = root{1} /\
        (forall (k : int), 0 <= k < i{1} => out{1}.[4 + 2 * 32 + k] = in_0{1}.[k])
      ) 
      (32 - i{1}); last by auto => /> /#.
      auto => /> &hr *. do split;1,2,5:smt(). 
          * admit. 
          * move => k??. rewrite get_setE 1:#smt:(@W64 pow2_64). 
            case (68 + k = to_uint (offset_out{hr} + (of_int i{hr})%W64)) => ?. admit. admit. 
auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18; split.
    + rewrite /DecodePkNoOID => />; rewrite tP => i Hi.
      rewrite get_of_list //=.
      case (0 <= i < 32).
        + move => ?.
          rewrite nth_cat size_to_list ifT 1:/# get_to_list H17 //=.
        + move => ?. 
          rewrite nth_cat size_to_list ifF 1:/# get_to_list -H12 //= /#.
    + rewrite /DecodeSkNoOID => />; rewrite tP => i Hi. rewrite -!get_to_list.
      case (0 <= i < 4).
        + move => ?. 
          rewrite of_listK; [by rewrite !size_cat !size_to_list H2 size_W32toBytes |].
          do ! (rewrite nth_cat !size_cat !size_to_list H2 size_W32toBytes //= ifT 1:/#).
          rewrite nth_cat !size_cat !size_to_list size_W32toBytes //= ifT 1:/#.
          rewrite nth_cat size_W32toBytes ifT 1:/# W32toBytes_zero_nth //= H8 //=.
      case (4 <= i < 4 + 32).
        + simplify => ? _. 
          rewrite get_of_list //=.
          rewrite nth_cat !size_cat !size_to_list size_W32toBytes H2 //= ifT 1:/#.
          rewrite nth_cat !size_cat !size_to_list size_W32toBytes H2 //= ifT 1:/#.
          rewrite nth_cat !size_cat !size_to_list size_W32toBytes //= ifT 1:/#.  
          rewrite nth_cat size_W32toBytes //= ifF 1:/# -H9 //= /#.  
      case (4 + 32 <= i < 4 + 2 * 32).
        + simplify => ? _ _.
          rewrite get_of_list //=.
          rewrite nth_cat !size_cat !size_to_list size_W32toBytes H2 //= ifT 1:/#.
          rewrite nth_cat !size_cat !size_to_list size_W32toBytes H2 //= ifT 1:/#.
          rewrite nth_cat !size_cat !size_to_list size_W32toBytes //= ifF 1:/# -H10 //= /#.  
      case (4 + 2*32 <= i < 4 + 3*32).     
        + simplify => ? _ _ _.
          rewrite get_of_list //=.
          rewrite nth_cat !size_cat !size_to_list size_W32toBytes H2 //= ifT 1:/#.
          rewrite nth_cat !size_cat !size_to_list size_W32toBytes H2 //= ifF 1:/# -H18 /#.
      move => ????.      
      rewrite get_to_list of_listK; [by rewrite !size_cat !size_to_list size_W32toBytes H2|].
      rewrite nth_cat !size_cat !size_to_list size_W32toBytes H2 //= ifF 1:/# -H11 /#.
qed.
