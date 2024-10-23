pragma Goals : printall.

require import AllCore IntDiv.

(* Lemmas about how the address is changed by each function in the Jasmin implementation *)
(* Thash_f = RandHash => Handled in Correctness Hash *)

require import Parameters XMSS_IMPL.
require import Termination.

require import Array8 Array32 Array64 Array2144.

from Jasmin require import JModel.

(*

set_layer_addr 		updates a.[0]
set_tree_addr 		updates a.[1] and a.[2]
set_type	 		updates a.[3]
set_ots_addr 		updates a.[4]
set_chain_addr 		updates a.[5]
set_hash_addr 		updates a.[6]
set_ltree_addr 		updates a.[4]
set_tree_height 	updates a.[5]
set_tree_index 		updates a.[6]
set_key_and_mask 	updates a.[7]

*)

(** -------------------------------------------------------------------------------------------- **)

lemma addr_prop_thash_f (a : W32.t Array8.t): 
    hoare[
      M(Syscall).__thash_f : 
      arg.`3 = a 
      ==> 
      res.`2.[0] = a.[0] /\
      res.`2.[1] = a.[1] /\
      res.`2.[2] = a.[2] /\
      res.`2.[3] = a.[3] /\
      res.`2.[4] = a.[4] /\
      res.`2.[5] = a.[5] /\
      res.`2.[6] = a.[6]
    ].
proof.
proc => /=.
call (: true) => //.
seq 10 : #pre; first by do (auto; call (: true) => //).
seq 1 : #post; first by inline; auto.
seq 2 : #pre; first by do call (: true) => //.
while (0 <= to_uint i <= 32 /\ #pre); last by auto. 
auto => /> &hr *; split => [| *]. 
  + rewrite to_uintD_small /#.
  + rewrite to_uintD_small 1:/# #smt:(@W64).
qed.

lemma addr_prop_thash_h (a : W32.t Array8.t): 
    hoare[
      M(Syscall).__thash_h : 
      arg.`4 = a 
      ==> 
      res.`2.[0] = a.[0] /\
      res.`2.[1] = a.[1] /\
      res.`2.[2] = a.[2] /\
      res.`2.[3] = a.[3] /\
      res.`2.[4] = a.[4] /\
      res.`2.[5] = a.[5] /\
      res.`2.[6] = a.[6]
    ].
proof.
proc => /=.
call (: true) => //.
seq 5 : #pre; first by auto; call (: true) => //; auto.
seq 1 : #post; first by inline; auto.
seq 3 : #pre; first by auto; do call (: true) => //.
seq 1 : #pre; first by inline; auto.
seq 3 : #pre; first by auto; do call (: true) => //.
seq 1 : #pre; first by inline; auto.
seq 3 : #pre; first by auto; do call (: true) => //.
while (0 <= to_uint i <= 64 /\ #pre); last by auto. 
auto => /> &hr *; split => [| *]. 
  + rewrite to_uintD_small /#.
  + rewrite to_uintD_small 1:/# #smt:(@W64).
qed.

(** -------------------------------------------------------------------------------------------- **)

lemma addr_prop_gen_chain (a : W32.t Array8.t) (_start_ _steps_ : W32.t) :
    hoare [
      M(Syscall).__gen_chain_inplace : 
      arg.`5 = a 
      ==>  
      res.`2.[0] = a.[0] /\
      res.`2.[1] = a.[1] /\
      res.`2.[2] = a.[2] /\
      res.`2.[3] = a.[3] /\
      res.`2.[4] = a.[4] /\
      res.`2.[5] = a.[5]
    ].
proof.
proc => /=.   
while (#post); last by auto => /> *; smt(@W32 pow2_32).
wp.
inline M(Syscall).__thash_f_ M(Syscall)._thash_f.
auto.
ecall (addr_prop_thash_f addr). 
auto; inline.
auto => /> /#. 
qed.

lemma p_addr_prop_gen_chain (a : W32.t Array8.t) (_start_ _steps_ : W32.t) :
    phoare [
      M(Syscall).__gen_chain_inplace : 
      arg.`5 = a /\
      0 <= to_uint start /\
      0 <= to_uint steps <= XMSS_WOTS_W /\
      0 <= to_uint (start + steps) <= XMSS_WOTS_W
      ==>  
      res.`2.[0] = a.[0] /\
      res.`2.[1] = a.[1] /\
      res.`2.[2] = a.[2] /\
      res.`2.[3] = a.[3] /\
      res.`2.[4] = a.[4] /\
      res.`2.[5] = a.[5]
    ] = 1%r.
proof.
by conseq gen_chain_inplace_ll (addr_prop_gen_chain a _start_ _steps_);  auto.
qed.


lemma addr_prop_expand_seed (a : W32.t Array8.t) :
    hoare [
        M(Syscall).__expand_seed : 
        arg.`4 = a 
        ==> 
        res.`2.[0] = a.[0] /\
        res.`2.[1] = a.[1] /\
        res.`2.[2] = a.[2] /\
        res.`2.[3] = a.[3] /\
        res.`2.[4] = a.[4]
    ].
proof.
proc => /=.
seq 3 : #pre; first by auto.
seq 2 : #post; first by inline; auto.
seq 2 : #pre; first by auto; call (: true) => //.
while (#post); last by auto.
seq 1 : #pre; first by inline; auto.
do (auto; call (: true) => //). 
qed.

lemma addr_prop_pkgen (a : W32.t Array8.t) :
    hoare [
      M(Syscall).__wots_pkgen :
      arg.`4 = a 
      ==>
      res.`2.[0] = a.[0] /\
      res.`2.[1] = a.[1] /\
      res.`2.[2] = a.[2] /\
      res.`2.[3] = a.[3] /\
      res.`2.[4] = a.[4]
    ].
proof.
proc => /=.
seq 2 : #post.
  + inline M(Syscall).__expand_seed_ M(Syscall)._expand_seed.
    wp.
    ecall (addr_prop_expand_seed addr).
    auto => />.
while (#post); last by auto.
seq 2 : #pre; first by inline; auto. 
seq 2 : #pre.
  + inline M(Syscall).__gen_chain_inplace_ M(Syscall)._gen_chain_inplace.
    wp.
    ecall (addr_prop_gen_chain addr1 start0 steps0).
    auto => /> /#.
auto => /> /#.
qed.

lemma addr_prop_pk_from_sig (a : W32.t Array8.t) :
    hoare [
      M(Syscall).__wots_pk_from_sig :
      arg.`5 = a
      ==>
      res.`2.[0] = a.[0] /\
      res.`2.[1] = a.[1] /\
      res.`2.[2] = a.[2] /\
      res.`2.[3] = a.[3] /\
      res.`2.[4] = a.[4]
    ].
proof.
proc => /=.
inline M(Syscall).__chain_lengths_ M(Syscall)._chain_lengths M(Syscall).__chain_lengths.
seq 21 : #pre; first by do (auto; call (: true) => //).
while (#post); last by auto.
inline M(Syscall).__gen_chain_inplace_ M(Syscall)._gen_chain_inplace.
wp. 
ecall (addr_prop_gen_chain addr1 start1 steps1).
auto; call (: true) => //.
inline; auto => /> /#. 
qed.

(** -------------------------------------------------------------------------------------------- **)

lemma addr_prop_ltree (a : W32.t Array8.t) :
    hoare [
      M(Syscall).__l_tree :
      arg.`4 = a
      ==>
      res.`3.[0] = a.[0] /\
      res.`3.[1] = a.[1] /\
      res.`3.[2] = a.[2] /\
      res.`3.[3] = a.[3] /\
      res.`3.[4] = a.[4]
    ].
proof.
proc => //.
seq 7 : #post; last by call (: true) => //; auto.
seq 3 : #pre; first by auto.
seq 3 : (#post /\ l = W64.of_int 67); first by inline; auto.
while (#post); last by auto.
seq 4 : #post; last first.
  + seq 3 : #post; last by inline; auto.
    seq 2 : #post; first by auto.    
    if; [ auto; call (: true) => //= |]; auto. 
seq 2 : #post; first by auto.
while (#post); last by auto.
auto.
call (: true) => //.
auto.
ecall (addr_prop_thash_h addr).
do 2! (call (: true) => //; auto).
inline; auto => /> /#. 
qed.

lemma addr_prop_compute_root (a : W32.t Array8.t) :
    hoare [
      M(Syscall).__compute_root :
      arg.`6 = a
      ==>
      res.`2.[0] = a.[0] /\
      res.`2.[1] = a.[1] /\
      res.`2.[2] = a.[2] /\
      res.`2.[3] = a.[3] /\
      res.`2.[4] = a.[4]
    ].    
proof.
proc => /=.
ecall (addr_prop_thash_h addr).
seq 5 : #pre; first by auto.
seq 1 : #pre.
  + if; last by auto; do 2! (call (: true) => //). 
    do 2! (auto; call (: true) => //).
seq 1 : #pre; first by auto. 
conseq  (: _ ==> 
  addr.[0] = a.[0] /\
  addr.[1] = a.[1] /\
  addr.[2] = a.[2] /\
  addr.[3] = a.[3] /\
  addr.[4] = a.[4]
); first by auto => /> /#.
seq 2 : #post; last by inline; auto. 
while (#post); last by auto.
seq 7 : #post; last by auto.
seq 6 : #post; first by inline; auto.
if.
    + auto; call (: true) => //.
      auto. 
      ecall (addr_prop_thash_h addr). 
      auto => /> /#.
    + auto; call (: true) => //.
      auto. 
      ecall (addr_prop_thash_h addr). 
      auto => /> /#.
qed.


lemma addr_prop_expand_sedd (a : W32.t Array8.t) :
    hoare [
      M(Syscall).__expand_seed :
      arg.`4 = a
      ==> 
      res.`2.[0] = a.[0] /\
      res.`2.[1] = a.[1] /\
      res.`2.[2] = a.[2] /\
      res.`2.[3] = a.[3] /\ 
      res.`2.[4] = a.[4] /\ 
      res.`2.[5] = W32.of_int 67 /\
      res.`2.[6] = W32.zero /\ 
      res.`2.[7] = W32.zero
    ].
proof.
proc => /=.
seq 3 : #pre; first by auto.

conseq (:
  addr.[0] = a.[0] /\
  addr.[1] = a.[1] /\
  addr.[2] = a.[2] /\
  addr.[3] = a.[3] /\
  addr.[4] = a.[4] /\
  addr.[5] = a.[5] /\
  addr.[6] = a.[6] /\
  addr.[7] = a.[7] 
  ==> 
  _
); first by auto.


 
seq 2 : (
    #{/~addr.[6] = a.[6]}{/~addr.[7] = a.[7]}pre /\ 
    addr.[6] = W32.zero /\
    addr.[7] = W32.zero
); first by inline; auto.

seq 2 : #pre; first by do 3! (auto; call (: true)). 

while (
  0 <= i <= 67 /\
  #{/~addr.[5] = a.[5]}pre /\
  (i <> 0 => addr.[5] = W32.of_int i)
); last first.

admit.

seq 1 : (#pre /\ addr.[5] = W32.of_int i); first by inline;auto.
do ! (auto; call (: true)).
auto => /> *. 
split => [/# | ?].
admit.
