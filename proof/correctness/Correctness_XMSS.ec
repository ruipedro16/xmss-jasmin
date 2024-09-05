pragma Goals : printall.

require import AllCore List RealExp IntDiv Distr DList.
from Jasmin require import JModel JArray.

require import Types Params Parameters Address Notation Hash Primitives Wots XMSS_MT_PRF.
require import XMSS_IMPL.
require import Repr. 

require import Array4 Array8 Array32 Array64 Array68 Array96 Array132 Array136 Array352 Array2144.
require import WArray32 WArray96 WArray136.

require import Correctness_Address Correctness_Mem Correctness_Hash.
require import Utils.

require import BitEncoding.
(*---*) import BitChunking.

(*** Treehash kg ***)

lemma treehash_kg_correct :
    equiv [
      M(Syscall).__treehash ~ TreeHash.treehash :
      true
      ==>
      to_list res{1}.`1 = res{2}.`1 (* we ignore the second part of the result in the proof for kg *)
    ].
proof.
proc.
seq 7 0 : (#pre); first by auto.
admit.
qed.

(*** Key Gen ***)

lemma _memset_nseq : 
    hoare [
      M(Syscall).__memset_zero_u8 :
      true
      ==>
      to_list res = nseq 4 W8.zero
    ].
proof.
proc.
while (
  0 <= to_uint i <= 4 /\
  forall (k : int), 0 <= k < to_uint i => a.[k] = W8.zero
). 
    + auto => /> &hr *; do split; 1,2:smt(@W64).
      move => ???. rewrite get_setE #smt:(@W64).
    + auto => /> &hr; split; [smt() |]. move => ? i???. 
      have ->: to_uint i = 4 by smt(@W64 pow2_64).
      move => ?. 
      apply (eq_from_nth witness); [ rewrite size_to_list size_nseq //= |].
      rewrite size_to_list => *. 
      rewrite nth_nseq 1:/# get_to_list /#.
qed.

require import Termination.

lemma get8_nth (x : W8.t list) (i : int) :
    0 <= i < 96 =>
      get8 (WArray96.of_list x) i = nth W8.zero x i.
proof.
move => H.
rewrite /get8 get_of_list; [assumption | trivial].
qed.

lemma memset_nseq : 
    phoare [ M(Syscall).__memset_zero_u8 : true ==>
       to_list res = nseq 4 W8.zero] = 1%r
          by conseq memset_zero_ll _memset_nseq; auto.

lemma xmss_kg_no_oid : 
    n = XMSS_N /\ 
    d = XMSS_D =>
    equiv [
      M(Syscall).__xmssmt_core_keypair ~ XMSS_MT_PRF.kg :
      true 
      ==>
(*      res{2}.`1 = EncodeSk_NoOID res{1}.`2 /\
      res{2}.`2 = EncodePk_NoOID res{1}.`1
*)
      true
    ].
proof.
rewrite /XMSS_N => [#] ??. 
proc.
seq 3 2 : (true); first by auto. 
seq 0 4 : (
  #pre /\
  size sk_seed{2}  = n /\
  size sk_prf{2}   = n /\
  size pub_seed{2} = n /\
  size root{2}     = n
); first by auto => />; rewrite size_nseq /#.
swap {2} [3..5] -2.
seq 1 3 : (
  #pre /\
  to_list seed_p{1} = sk_seed{2} ++ sk_prf{2} ++ pub_seed{2}
).
    + inline {1}; wp; sp; auto => />. 
      rnd{1}. do 3! rnd{2}. skip => /> &2 H0 H1 H2 H3 sk_seed0 ? sk_prf0 T1 pub_seed0? ; split. 
        - apply dmap_ll. rewrite /darray dmap_ll dlist_ll #smt:(@W8). 
        - move => ? a0.
          rewrite /darray dmap_comp /(\o) /get8 => H4.
          have E0: size sk_seed0 = 32 by smt(@DList).
          have E1: size sk_prf0 = 32 by smt(@DList). 
          have E2: size pub_seed0 = 32 by smt(@DList).
          do split; 1..3:smt().  
          apply (eq_from_nth witness).
               +  by rewrite size_to_list !size_cat E0 E1 E2. 
          move => i. rewrite size_to_list => Hi.
          rewrite !nth_cat size_cat E0 E1 //=.
          case (0 <= i < 32).
             * move => H. rewrite ifT 1:/# ifT 1:/#. admit.          
          case (32 <= i < 64).
             * move => H?. rewrite ifT 1:/# ifF 1:/#. admit.
          move => ??. 
          have H: 64 <= i < 96 by smt().
          rewrite ifF 1:/#.                     
          admit.
inline {1} M(Syscall).__xmssmt_core_seed_keypair.
sp 3 0.
seq 9 0 : (#pre); first by auto. 
seq 1 1 : (#pre /\ address{2} = top_tree_addr{1}).
    + inline {1}; wp; sp. 
      while {1} (0 <= i{1} <= 8 /\ forall (k : int), 0 <= k < i{1} => addr0{1}.[k] = W32.zero) (8 - i{1}).
         * auto => /> *; do split;1,2,4:smt(); move => k??; rewrite get_setE /#.
         * skip => /> *; split; [smt() |]; move => *; split; [smt() | move => ????; rewrite /zero_address; smt(@Array8)].
seq 1 1 : (#pre); first by inline {1}; auto => /> *; rewrite /set_layer_addr /#. 
seq 2 0 : (#pre /\ to_list idx{1} = nseq 4 W8.zero).
    + call {1} memset_nseq; auto. 
auto => />. 
seq 1 0 : (
  (* #pre without the second /\ *)
  pk0{1} = pk{1} /\
  seed0{1} = seed_p{1} /\
  size sk_seed{2} = n /\
  size sk_prf{2} = n /\ 
  size pub_seed{2} = n /\ 
  size root{2} = n /\
  to_list seed_p{1} = sk_seed{2} ++ sk_prf{2} ++ pub_seed{2} /\
  address{2} = top_tree_addr{1} /\
  to_list idx{1} = nseq 4 W8.zero /\

  forall (k : int), 0 <= k < 4 => sk0{1}.[k] = W8.zero
).
    + auto => /> ??????? H *; rewrite initE ifT 1:/#. 
      auto => />; rewrite ifT 1:/# -get_to_list H nth_nseq 1:/# //. 
seq 2 0 : (
    #pre /\
    forall (k : int), 0 <= k < 64 => buf1{1}.[k] = seed0{1}.[k]
); first by auto => /> *; rewrite initE ifT 1:/#; auto => />. 
seq 1 0 : (#pre /\ buf0{1} = buf1{1}); first by ecall {1} (_x_memcpy_u8u8_64_post buf1{1}); skip => />. 
seq 1 0 : (
  #pre /\ 
  forall (k : int), 0 <= k < 64 => sk0{1}.[4 + k] = seed0{1}.[k]
).
    + auto => /> &1 &2 ?????? H0 H1; split; move => ???; rewrite initE ifT 1:/#; auto => />; [rewrite ifF /# | rewrite ifT /#]. 
seq 2 0 : (
  (* from #pre *)
  pk0{1} = pk{1} /\
  seed0{1} = seed_p{1} /\
  size sk_seed{2} = n /\
  size sk_prf{2} = n /\
  size pub_seed{2} = n /\
  size root{2} = n /\
  to_list seed_p{1} = sk_seed{2} ++ sk_prf{2} ++ pub_seed{2} /\
  address{2} = top_tree_addr{1} /\
  to_list idx{1} = nseq 4 W8.zero /\
  (forall (k : int), 0 <= k < 4  => sk0{1}.[k] = W8.zero) /\
  (forall (k : int), 0 <= k < 64 => sk0{1}.[4 + k] = seed0{1}.[k]) /\

  forall (k : int), 0 <= k < 32 => bufn1{1}.[k] = seed0{1}.[64 + k]
); first by auto => /> *; rewrite initE ifT /#.
seq 1 0 : (#pre /\ bufn0{1} = bufn1{1}); first by ecall {1} (_x_memcpy_u8u8_post bufn1{1}); skip => />. 
seq 1 0 : (
    #pre /\
    forall (k : int), 0 <= k < 32 => sk0{1}.[4 + 3 *32 + k] = seed0{1}.[64 + k]
).
    + auto => /> *; do split; move => *; rewrite initE ifT 1:/#; auto => />; [| | rewrite ifT /#]; rewrite ifF /#. 
seq 2 0 : (
  (* from #pre *)
  seed0{1} = seed_p{1} /\
  size sk_seed{2} = n /\
  size sk_prf{2} = n /\
  size pub_seed{2} = n /\
  size root{2} = n /\
  to_list seed_p{1} = sk_seed{2} ++ sk_prf{2} ++ pub_seed{2} /\
  address{2} = top_tree_addr{1} /\
  to_list idx{1} = nseq 4 W8.zero /\
  (forall (k : int), 0 <= k < 4 => sk0{1}.[k] = W8.zero) /\
  (forall (k : int), 0 <= k < 64 => sk0{1}.[4 + k] = seed0{1}.[k]) /\
  (forall (k : int), 0 <= k < 32 => sk0{1}.[4 + 3 * 32 + k] = seed0{1}.[64 + k]) /\


  (forall (k : int), 0 <= k < 32 => bufn1{1}.[k] = sk0{1}.[4 + 3*32 + k])
); first by auto => /> *; rewrite initE 1:/#.
seq 1 0 : (#pre /\ bufn0{1} = bufn1{1}); first by ecall {1} (_x_memcpy_u8u8_post bufn1{1}); skip => />. 
seq 1 0 : (
  #pre /\
  forall (k : int), 0 <= k < 32 => pk{1}.[32 + k] = bufn0{1}.[k]
).
    + auto => /> &1 &2 ?????? H0 H1 H2 H3 k??. rewrite H3 1:/# H2 1:/#. admit.
admit.
qed.


lemma xmss_kg_correct :
    equiv [
      M(Syscall).xmss_keypair_jazz ~ XMSS_MT_PRF.kg:
      true
      ==>
      res{2}.`1 = EncodeSk res{1}.`2 /\
      res{2}.`2 = EncodePk res{1}.`1
    ].
proof.
proc.
  seq 1 13 : (#post); last by auto.
seq 0 6 : (
  size sk_seed{2}  = n /\
  size sk_prf{2}   = n /\
  size pub_seed{2} = n
); first by auto => />; rewrite size_nseq #smt:(ge0_n).  
inline {1} M(Syscall).__xmss_keypair.
seq 2 0 : (#pre); first by auto.
seq 4 0 : (#pre /\ oid{1} = BSWAP_32 W32.one).
  + auto. 




(* This needs to be changed accordingly *)
inline M(Syscall).__xmssmt_core_keypair_ M(Syscall)._xmssmt_core_keypair M(Syscall).__xmssmt_core_keypair.
seq 11 0 : (#pre); first by auto.  (* E possivel que isto esteja errado *)
seq 0 1 : (#pre /\ address{2} = zero_address); first by auto.
seq 1 3 : (#pre /\ to_list seed_p{1} = sk_seed{2} ++ sk_prf{2} ++ pub_seed{2}).
  + inline {1}; sp; auto => />. 
(*
    rnd () (Array96.of_list witness).
    auto => /> *; do split. 
     - move => ?. rewrite of_listK
*)
admit.
inline  M(Syscall).__xmssmt_core_seed_keypair.



seq 9 3 : (#pre). (* this pre is wrong *)
  + admit.
seq 0 1 : (#pre /\ sk{2} = EncodeSk sk{1}).
  + admit.
seq 0 1 : (#post); last by skip. 
  + admit.
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
