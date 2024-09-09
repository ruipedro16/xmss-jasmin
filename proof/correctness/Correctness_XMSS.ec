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

lemma random_bytes_equiv_flipped :
    n = XMSS_N =>
    equiv [
      XMSS_MT_PRF.sample_randomness ~ Syscall.randombytes_96  :
      true 
      ==>
      to_list res{2} = res{1}.`1 ++ res{1}.`2 ++ res{1}.`3
    ].  
proof.
move => H. 
symmetry.
admit.
qed.

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

(* At this point were in memcpy(sk, seed, 2 * params->n); *)
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
    + exists * root{1}, pk0{1}. 
      elim * => P0 P1.
      admit. 
seq 1 0 : (
  #pre /\
  (forall (k : int), 0 <= k < 32 => sk0{1}.[4 + 2 * 32 + k] = nth witness root{2} k)
).
    + exists * sk0{1}, root{1}; elim * => P0 P1.
      call {1} (nbytes_copy_132_32_result P1 P0 W64.zero (W64.of_int(4 + 2*32))).
      do split. move => ?. simplify. admit. (* TODO: Rewrite lemma *)
      admit.
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
      have E : 100 <= i < 132 by smt().           
          rewrite get_to_list of_listK; [by rewrite !size_cat !size_to_list size_W32toBytes H2|].
          rewrite nth_cat !size_cat !size_to_list size_W32toBytes H2 //= ifF 1:/# -H11 /#.
qed.


(*** TODO: exported function ***)

(*** L Tree ***)

lemma ltree_correct (_pk : W8.t Array2144.t, _pub_seed : W8.t Array32.t, _addr : W32.t Array8.t) : 
    len = XMSS_WOTS_LEN /\ 
    n = XMSS_N =>
    equiv [
      M(Syscall).__l_tree ~ LTree.ltree :
      size pk{2} = len /\  
      (forall (t0 : W8.t list), t0 \in pk{2} => size t0 = 32) /\
      arg{1}.`2 = _pk /\
      arg{1}.`3 = _pub_seed /\
      arg{1}.`4 = _addr /\
      arg{2} = (EncodeWotsPk _pk, _addr, to_list _pub_seed)
      ==>
      to_list res{1}.`1 = res{2}.`1 /\ (* wots pk *)
      res{1}.`3 = res{2}.`2 (* address *)
    ].
proof.
rewrite /XMSS_WOTS_LEN /XMSS_N.
move => [#] len_val n_val.
proc. 
auto => />.
seq 3 1 : (#pre); first by auto. 
 
seq 1 1 : (#pre /\ _len{2} = to_uint l{1} /\ _len{2} = 67);  first by auto.
 
seq 2 1 : (
  addr{1} = address{2} /\
  pk{2} = EncodeWotsPk wots_pk{1} /\
  _seed{2} = to_list pub_seed{1} /\
  _len{2} = to_uint l{1} /\
  _len{2} = 67 /\
  size pk{2} = len /\
  (forall (t0 : W8.t list), t0 \in pk{2} => size t0 = 32)

); first by inline {1}; auto. 

seq 1 1 : (
  addr{1} = address{2} /\
  (forall (k : int), 0 <= k < 32 => wots_pk{1}.[k] = nth witness (nth witness pk{2} 0) k) /\ (* The first chunk is equal *)
  size pk{2} = len /\
  (forall (t0 : W8.t list), t0 \in pk{2} => size t0 = 32)
); last first.
    + ecall {1} (_x_memcpy_u8u8_post tmp{1}).
      auto => /> &1 &2 H0 *.  
      have E : forall (k : int), 0 <= k && k < len => size (nth witness pk{2} k) = 32 by smt(@List). 
      apply (eq_from_nth witness); [by rewrite size_to_list E /# |]. 
      rewrite size_to_list => j?. 
      rewrite -H0 //= initiE //=.

(*
conseq (: _ ==>
  addr{1} = address{2} /\
  (forall (k : int), 0 <= k < 32 =>  wots_pk{1}.[k] = nth witness (flatten pk{2}) k) /\
  size pk{2} = len /\ 
    forall (t0 : W8.t list), t0 \in pk{2} => size t0 = 32
).
    + auto => /> &1 H0 H1 H2 addrL pkL H3 H4 H5 k??. 
      rewrite -nth_flatten.
         * rewrite H4 len_val //=.                      
         * rewrite (: size (nth witness pkL 0) = 32); [apply H5; smt(@List) | by []].
         * rewrite H3 //=; congr. 
           rewrite sumzE BIA.big_map /(\o) //= -(StdBigop.Bigint.BIA.eq_big_seq (fun _ => 32)) 1:#smt:(@List) big_constz count_predT. 
           rewrite size_take //= ifT 1:/# //=.
*)
(* At this point, we only have the while loop *)

while (
  addr{1} = address{2} /\
  _seed{2} = to_list pub_seed{1} /\
  
  size pk{2} = len /\
  (forall (t0 : W8.t list), t0 \in pk{2} => size t0 = 32) /\
  
    1 <= _len{2} <= 67 /\ 
  _len{2} = to_uint l{1} /\

  forall (k : int), 0 <= k < to_uint (l{1} `>>` W8.one) => wots_pk{1}.[k] = nth witness (flatten pk{2}) k

); last first.
auto => /> &1 H0 H1 H2 *; do split.
    + smt().
    + smt(). 
    + move => k??. rewrite /EncodeWotsPk. admit.
    + smt(). 
    + smt(@W64 pow2_64). 
    + move => iL pkL pkR Ha Hb Hc Hd He Hf Hg k*. 
      rewrite Hg; [rewrite shr_1 |]. admit.
      rewrite -nth_flatten 1:/#. 
      rewrite (: size (nth witness pkR 0) = 32) 1:#smt:(@List) //=. 
      congr. 
      rewrite sumzE BIA.big_map /(\o) //= -(StdBigop.Bigint.BIA.eq_big_seq (fun _ => 32)) 1:#smt:(@List) big_constz count_predT size_take //=. 
      rewrite ifT 1:/# //=.


seq 2 0 : (
  #pre /\
  to_uint parent_nodes{1} = floor (_len{2}%r / 2%r)
).
    + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6.
      rewrite truncate_1_and_63 shr_1. admit.

seq 2 2 : (
  #pre /\
  forall (k : int)
). 





(*** Treehash ***)

(******* exported functions ********)
