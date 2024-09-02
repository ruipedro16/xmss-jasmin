pragma Goals : printall.

require import AllCore List RealExp IntDiv.
from Jasmin require import JModel.

require import XMSS_IMPL.
require import Types Address Notation Hash Primitives Params Parameters Utils Util.
require import Correctness_Mem.

require import Array8 Array32 Array64 Array96 Array128.


axiom hash_96 (x : W8.t Array96.t) :
    phoare[M(Syscall).__core_hash_96 : arg.`2 = x ==> to_list res = Hash (to_list x)] = 1%r.

axiom hash_128 (x : W8.t Array128.t) :
    phoare[M(Syscall).__core_hash_128 : arg.`2 = x ==> to_list res = Hash (to_list x)] = 1%r.

lemma prf_correctness (a b : W8.t Array32.t) :
    prf_padding_val = XMSS_HASH_PADDING_PRF /\ 
    padding_len = XMSS_PADDING_LEN =>
    equiv [
    M(Syscall).__prf ~ Hash.prf : 
    arg{1}.`2 = a /\ arg{1}.`3 = b /\ arg{2} = (to_list a, to_list b) 
    ==>
    res{2} = to_list res{1}
    ].
proof.
rewrite /XMSS_HASH_PADDING_PRF /XMSS_PADDING_LEN => [#] ??.
proc.
seq 9 2 : (buf{2} = to_list buf{1}); last first.
  + inline M(Syscall).__core_hash__96 M(Syscall)._core_hash_96; wp; sp.
    ecall {1} (hash_96 buf{1}); auto => /> /#.
seq 3 0 : (#pre); 1:auto.
seq 1 1 : (#pre /\ padding{2} = to_list padding_buf{1}).
  + call {1} (ull_to_bytes_correct (of_int 3)%W64); auto => />. 
seq 1 0 : (
  key{2} = to_list key{1} /\
  in_0{2} = to_list in_0{1} /\
  padding{2} = to_list padding_buf{1} /\ 
  forall (k : int), 0 <= k < 32 => buf{1}.[k] = nth witness padding{2} k
); first by auto => /> *; smt(@Array96 @List).
seq 1 0 : (#pre /\ aux{1} = key{1}); first by ecall {1} (_x_memcpy_u8u8_post key{1}); auto => />.
seq 1 0 : (#pre /\ forall (k : int), 32 <= k < 64 => buf{1}.[k] = nth witness key{2} (k - 32)).
    + auto => />; smt(@Array96 @List).
seq 1 0 : (
  key{2} = to_list key{1} /\
  in_0{2} = to_list in_0{1} /\
  padding{2} = to_list padding_buf{1} /\ 
  (forall (k : int), 0 <= k < 32 => buf{1}.[k] = nth witness padding{2} k) /\
  (forall (k : int), 32 <= k < 64 => buf{1}.[k] = nth witness key{2} (k - 32)) /\
  aux{1} = in_0{1}
).
    + ecall {1} (_x_memcpy_u8u8_post in_0{1}); auto => /> /#.
seq 1 0 : (
  key{2} = to_list key{1} /\ size key{2} = 32 /\
  in_0{2} = to_list in_0{1} /\ size in_0{2} = 32 /\
  padding{2} = to_list padding_buf{1} /\  size padding{2} = 32 /\
  (forall (k : int), 0 <= k < 32 => buf{1}.[k] = nth witness padding{2} k) /\
  (forall (k : int), 32 <= k < 64 => buf{1}.[k] = nth witness key{2} (k - 32)) /\
  (forall (k : int), 64 <= k < 96 => buf{1}.[k] = nth witness in_0{2} (k - 64))
).
    + auto => /> *; do split; smt(@Array96 @List).
    + auto => /> *; rewrite !/to_list !/mkseq -!iotaredE => /> /#. 
qed.

lemma prf_keygen_correctness (a : W8.t Array64.t, b : W8.t Array32.t) :
    prf_padding_val = XMSS_HASH_PADDING_PRF /\
    prf_kg_padding_val = XMSS_HASH_PADDING_PRF_KEYGEN /\ 
    padding_len = XMSS_PADDING_LEN =>
    equiv [
    M(Syscall).__prf_keygen ~ Hash.prf_keygen : 
    arg{1}.`2 = a /\ arg{1}.`3 = b /\ arg{2} = (to_list a, to_list b) 
    ==>
    res{2} = to_list res{1}
    ].
proof.
rewrite /XMSS_HASH_PADDING_PRF_KEYGEN /XMSS_PADDING_LEN => [#] ???.
proc => //=.
seq 9 2 : (buf{2} = to_list buf{1}); last first.
  + inline M(Syscall).__core_hash__128 M(Syscall)._core_hash_128; wp; sp.
    ecall {1} (hash_128 buf{1}); auto => /> /#.
seq 3 0 : (#pre); 1:auto.
seq 1 1 : (#pre /\ padding{2} = to_list padding_buf{1}).
  + call {1} (ull_to_bytes_correct (of_int 4)%W64); auto => />. 
seq 1 0 : (
  key{2} = to_list key{1} /\
  in_0{2} = to_list in_0{1} /\
  padding{2} = to_list padding_buf{1} /\ 
  forall (k : int), 0 <= k < 32 => buf{1}.[k] = nth witness padding{2} k
); first by auto => /> *; smt(@Array128 @List).
seq 1 0 : (#pre /\ aux{1} = key{1}); first by ecall {1} (_x_memcpy_u8u8_post key{1}); auto => />.
seq 1 0 : (#pre /\ forall (k : int), 32 <= k < 64 => buf{1}.[k] = nth witness key{2} (k - 32)).
    + auto => />; smt(@Array128 @List).
seq 1 0 : (
  key{2} = to_list key{1} /\
  in_0{2} = to_list in_0{1} /\
  padding{2} = to_list padding_buf{1} /\ 
  (forall (k : int), 0 <= k < 32 => buf{1}.[k] = nth witness padding{2} k) /\
  (forall (k : int), 32 <= k < 64 => buf{1}.[k] = nth witness key{2} (k - 32)) /\
  aux_0{1} = in_0{1}
).
    + ecall {1} (_x_memcpy_u8u8_64_post in_0{1}); auto => /> /#.
seq 1 0 : (
  key{2} = to_list key{1} /\ size key{2} = 32 /\
  in_0{2} = to_list in_0{1} /\ size in_0{2} = 64 /\
  padding{2} = to_list padding_buf{1} /\  size padding{2} = 32 /\
  (forall (k : int), 0 <= k < 32 => buf{1}.[k] = nth witness padding{2} k) /\
  (forall (k : int), 32 <= k < 64 => buf{1}.[k] = nth witness key{2} (k - 32)) /\
  (forall (k : int), 64 <= k < 128 => buf{1}.[k] = nth witness in_0{2} (k - 64))
).
    + auto => /> *; do split; smt(@Array128 @List).
    + auto => /> *; rewrite !/to_list !/mkseq -!iotaredE => /> /#. 
qed.


 
lemma rand_hash_correct (i0 i1: nbytes, _pub_seed : W8.t Array32.t, _in : W8.t Array64.t, a : W32.t Array8.t) :
    padding_len = XMSS_PADDING_LEN /\ 
    prf_padding_val = XMSS_HASH_PADDING_PRF /\
    padding_len = XMSS_PADDING_LEN /\ 
    n = XMSS_N /\
    size i0 = n /\ 
    size i1 = n =>
    equiv [
      M(Syscall).__thash_h ~ Hash.rand_hash :
      arg{1}.`2 = (merge_nbytes_to_array i0 i1) /\
      arg{1}.`3 = _pub_seed /\
      arg{1}.`4 = a /\
      arg{2} = (i0, i1, to_list _pub_seed, a)
      ==>
      to_list res{1}.`1 = res{2}.`1 /\
      res{1}.`2 = res{2}.`2
    ].
proof.
rewrite /XMSS_PADDING_LEN /XMSS_HASH_PADDING_PRF /XMSS_PADDING_LEN /XMSS_N => [#] ??? nval.
rewrite nval => ??.
proc; auto => />.
seq 3 0 : (#pre); 1:auto.
seq 1 1 : (#pre /\ padding{2} = to_list aux{1} /\ size padding{2} = 32).
    + by call {1} (ull_to_bytes_correct W64.one); skip => /> &1 &2 *; rewrite size_to_list.
swap {1} [2..3] -1.

(* conseq to rewrite #pre *)
conseq (: 
  to_list in_0{1} = _left{2} ++ _right{2} /\
  _seed{2} = to_list pub_seed{1} /\ 
  address{2} = addr{1} /\
  padding{2} = to_list aux{1} /\ 
  
  size _left{2} = 32 /\
  size _right{2} = 32 /\
  size padding{2} = 32

  ==> 
  _
).
auto => /> &1 *. rewrite /merge_nbytes_to_array. apply (eq_from_nth witness); [ rewrite size_cat size_to_list /# | smt(@List @Array64) ]. 
(* ; first by auto => /> &1 ?; split; move => k Hk1 Hk2; rewrite /merge_nbytes_to_array initE; auto => />; rewrite ifT 1:/#; auto => /> /#. => se usar forall em vez de in=left++right*) 
seq 2 2 : (#pre /\ addr_bytes{2} = to_list addr_as_bytes{1}).
    + inline {1} M(Syscall).__set_key_and_mask; ecall {1} (addr_to_bytes_correctness addr{1}); auto => /> /#. 
seq 1 0 : (
  #pre /\
  forall (k : int), 0 <= k < 32 => buf{1}.[k] = nth witness padding{2} k
); first by auto => /> *; rewrite initE ifT 1:/#; auto => /> /#.
 
seq 1 1 : (
  to_list in_0{1} = _left{2} ++ _right{2} /\
  
  _seed{2} = to_list pub_seed{1} /\ 
  address{2} = addr{1} /\
  addr_bytes{2} = to_list addr_as_bytes{1} /\

  size _left{2} = n /\
  size _right{2} = n /\
  size padding{2} = 32 /\
  size key{2} = 32 /\

  (* Tmp *)
  key{2} = to_list aux{1} /\

  (* Towards #post *)
  forall (k : int), 0 <= k < 32 => buf{1}.[k] = nth witness padding{2} k
).
    + inline {1} M(Syscall).__prf_ M(Syscall)._prf; wp; sp.
      exists * in_01{1}, key0{1}; elim * => _P1 _P2; call {1} (prf_correctness _P1 _P2); first by split; assumption. 
      skip => /> &1 &2 *. rewrite size_to_list; do split; 1,2: rewrite nval; assumption.
(* Remove hash from #post *)
seq 11 6 : (
  addr{1} = address{2} /\
  to_list buf{1} = padding{2} ++ key{2} ++ nbytexor (_left{2} ++ _right{2}) (bitmask_0{2} ++ bitmask_1{2})
); last first. 
    + inline {1}  M(Syscall)._core_hash_128. wp. ecall {1} (hash_128 in_00{1}). auto => /> &1 &2 ??; move => ->; congr.      
seq 1 0 : (
    #pre /\
    forall (k : int), 0 <= k < 32 => buf{1}.[32 + k] = nth witness key{2} k
).
    + auto => /> &1 &2 *; split; move => ???; rewrite initE ifT 1:/#; auto => />; [rewrite ifF /# | rewrite ifT /#].
seq 2 2 : (#pre).
    + inline {1} M(Syscall).__set_key_and_mask; ecall {1} (addr_to_bytes_correctness addr{1}); auto => /> /#.
(* Bitmask appears first here *)
seq 2 1 : (
  to_list in_0{1} = _left{2} ++ _right{2} /\
  _seed{2} = to_list pub_seed{1} /\ 
  address{2} = addr{1} /\
  addr_bytes{2} = to_list addr_as_bytes{1} /\

  size _left{2} = n /\
  size _right{2} = n /\
  size padding{2} = 32 /\
  size key{2} = 32 /\
  
  (* Bitmask *)
  (forall (k : int), 0 <= k < 32 => bitmask{1}.[k] = nth witness bitmask_0{2} k) /\
  size bitmask_0{2} = n /\

  (* Towards #post *)
  (forall (k : int), 0 <= k < 32 => buf{1}.[k] = nth witness padding{2} k) /\
  (forall (k : int), 0 <= k < 32 => buf{1}.[32 + k] = nth witness key{2} k)
).
    + inline {1} M(Syscall).__prf_ M(Syscall)._prf; wp; sp.
      exists * in_01{1}, key0{1}; elim * => _P1 _P2; call {1} (prf_correctness _P1 _P2); first by split; assumption.
      skip => /> &1 &2 *. split; [| rewrite size_to_list /# ]. move => k Hk0 Hk1. rewrite initiE 1:/#.
      auto => />. rewrite ifT; split; [| move => _]; assumption.
seq 2 2 : (#pre).
    + inline {1} M(Syscall).__set_key_and_mask; ecall {1} (addr_to_bytes_correctness addr{1}); auto => /> /#.
seq 2 1 : (
  #pre /\ 
  (forall (k : int), 0 <= k < 32 => bitmask{1}.[32 + k] = nth witness bitmask_1{2} k) /\
  size bitmask_1{2} = n
). 
    + inline {1} M(Syscall).__prf_ M(Syscall)._prf; wp; sp.
      exists * in_01{1}, key0{1}; elim * => _P1 _P2; call {1} (prf_correctness _P1 _P2); first by split; assumption.
      skip => /> &1 &2 *.
      do split; [| | by rewrite size_to_list /#]; move => ???; rewrite initE ifT 1:/#; auto => />; [rewrite ifF /# | rewrite ifT /# ].
 
(* Conseq to simplify #post *) 
conseq (: _ ==>
  size padding{2} = 32 /\
  size key{2} = 32 /\
  size bitmask_0{2} = 32 /\
  size bitmask_1{2} = 32 /\
  size _left{2} = 32 /\
  size _right{2} = 32 /\
  addr{1} = address{2} /\
  (forall (k : int), 0 <= k < 32 => buf{1}.[k] = nth witness padding{2} k) /\
  (forall (k : int), 0 <= k < 32 => buf{1}.[32 + k] = nth witness key{2} k) /\
  (forall (k : int), 0 <= k < 64 => buf{1}.[64 + k] = nth witness (nbytexor (_left{2} ++ _right{2}) (bitmask_0{2} ++ bitmask_1{2})) k)
).
    + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 buf_L H11 H12 H13 H14 H15 H16 H17. 
      apply (eq_from_nth witness). rewrite !size_cat size_to_list H3 H4 /nbytexor !size_map !size_zip !size_cat H1 H2 H6 H10 !nval //=.  
      move => i. rewrite size_to_list => Hi.
      rewrite get_to_list.
      case (0 <= i < 32). 
          * smt(@List @Array128).
      case (32 <= i < 64). 
          * move => ? _. rewrite nth_cat ifT; first by rewrite size_cat H3 H4 /#. rewrite nth_cat ifF 1:/#. smt(@List @Array128).
      move => Ht0 Ht1. 
      have H: 64 <= i < 128 by smt(). clear Ht0 Ht1 Hi.
      rewrite nth_cat ifF; first by rewrite size_cat H3 H4 /#.
      have ->: size (padding{2} ++ key{2}) = 64 by rewrite size_cat H3 H4.
      smt().

(* End of proof for conseq *)
 
while {1} ( 
  0 <= to_uint i{1} <= 64 /\

  size padding{2} = 32 /\ 
  size key{2} = 32 /\
  size bitmask_0{2} = 32 /\
  size bitmask_1{2} = 32 /\
  size _left{2} = 32 /\
  size _right{2} = 32 /\

  addr{1} = address{2} /\
  
  to_list in_0{1} = _left{2} ++ _right{2} /\
  to_list bitmask{1} = bitmask_0{2} ++ bitmask_1{2} /\

  (forall (k : int), 0 <= k < 32 => buf{1}.[k] = nth witness padding{2} k) /\
  (forall (k : int), 0 <= k < 32 => buf{1}.[32 + k] = nth witness key{2} k) /\

  (forall (k : int), 0 <= k < to_uint i{1} => 
    buf{1}.[64 + k] = 
      nth witness (_left{2} ++ _right{2}) (k) `^` nth witness (bitmask_0{2} ++ bitmask_1{2}) (k))
) (64 - to_uint i{1}).
    + auto => /> &hr ?? H0 H1 H2 H3 H4 H5 H6 H7 H8 H9.
      rewrite /nbytexor => H10 H11; do split; last by smt(@W64 pow2_64).
       * smt(@W64).
       * smt(@W64). 
       * move => *; rewrite get_setE; first by smt(@W64). rewrite ifF; first by smt(@W64 pow2_64). smt(). 
       * move => *; rewrite get_setE; first by smt(@W64). rewrite ifF; first by smt(@W64 pow2_64). smt(). 
       * move => k *. 
         have E0: forall (k : int), 0 <= k < 32 => in_0{hr}.[k] = nth witness _left{m} k by smt(@List @Array64). 
         have E1: forall (k : int), 0 <= k < 32 => in_0{hr}.[32 + k] = nth witness _right{m} k by smt(@List @Array64). 
         have E2: forall (k : int), 0 <= k < 32 => bitmask{hr}.[k] = nth witness bitmask_0{m} k by smt(@List @Array64). 
         have E3: forall (k : int), 0 <= k < 32 => bitmask{hr}.[32 + k] = nth witness bitmask_1{m} k by smt(@List @Array64). 
         case (0 <= k < 32).
           - move => ?. rewrite !(nth_cat witness) H2 H4 ifT 1:/# ifT 1:/# get_setE; [smt(@W64) |].
             case (64 + k = to_uint ((of_int 64)%W64 + i{hr})).
                + move => ?. congr; have ->: to_uint i{hr} = k by smt(@W64 pow2_64).
                    - apply E0; smt(). 
                    - apply E2; smt(). 
                + move => ?. rewrite H10; first by smt(@W64 pow2_64). congr; rewrite (nth_cat witness) ifT 1:/# //=.
           - move => H12. rewrite !(nth_cat witness) H2 H4 ifF 1:/# ifF 1:/# get_setE; [smt(@W64) |]. 
             case (64 + k = to_uint ((of_int 64)%W64 + i{hr})).
                + move => ?. have ->: to_uint i{hr} = k by smt(@W64 pow2_64). congr; smt(@List @Array64).
                + move => ?. rewrite H10; first by smt(@W64 pow2_64). 
                  rewrite !(nth_cat witness) ifF 1:/# ifF 1:/# H2 H4 //. 
    + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10; do split;1..4,6:smt(). 
       * apply /(eq_from_nth witness); first by rewrite size_cat size_to_list H6 H10 /#.
         rewrite size_to_list => i?; rewrite nth_cat get_to_list H6; case (i < n); smt(). 
       * move => bufL iL; do split.
           - move => *. smt(@W64).
           - move => Ht0 Ht1 Ht2 H11 H12 H13 H14. 
             have ->: to_uint iL = 64 by smt(@W64 pow2_64).
             clear Ht0 Ht1 Ht2.
             move => H15 H16 H17 H18.
             move => k Hk0 Hk1. 
             rewrite /nbytexor (nth_map witness); first by rewrite size_zip !size_cat H1 H2 H6 H10 nval /#. 
             auto => />.
             have ->: (nth witness (zip (_left{2} ++ _right{2}) (bitmask_0{2} ++ bitmask_1{2})) k).`1 = nth witness (_left{2} ++ _right{2}) k by smt(@List). 
             have ->: (nth witness (zip (_left{2} ++ _right{2}) (bitmask_0{2} ++ bitmask_1{2})) k).`2 = nth witness (bitmask_0{2} ++ bitmask_1{2}) k by smt(@List). 
             apply H18. smt(). 
qed.
