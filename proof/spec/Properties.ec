pragma Goals : printall.


require import AllCore List Distr RealExp IntDiv.
require (*  *) Subtype.

from Jasmin require import JModel.

require import Notation Address Primitives Wots XMSS.
require import XMSS_IMPL.

require import Array8.


import DList.
import NBytes.

(********************************** ADDRESS ***********************************)

lemma set_layer_addr_op_impl (addr : adrs, layer : int): 
    set_layer_addr_pre layer => 
        hoare[M(Syscall).__set_layer_addr : 
            arg = (addr, W32.of_int layer) ==> res = set_layer_addr addr layer].
proof. move => ?. proc. auto. qed.

lemma set_tree_addr_op_impl (address : adrs, tree_address : int):
    set_tree_addr_pre tree_address => 
        hoare[M(Syscall).__set_tree_addr : 
            arg = (address, W64.of_int tree_address) ==> res = set_tree_addr address tree_address].
proof. move => ?. proc. auto. qed.

lemma set_type_op_impl (address : adrs, _type : int):
    set_type_pre _type =>
        hoare[M(Syscall).__set_type :
            arg = (address, W32.of_int _type) ==> res = set_type address _type].
proof. move => ?. proc. auto. qed.

lemma set_ots_addr_op_impl (address : adrs, ots_addr : int):
    set_ots_addr_pre ots_addr => 
        hoare[M(Syscall).__set_ots_addr :
            arg = (address, W32.of_int ots_addr) ==> res = set_ots_addr address ots_addr].
proof. move => ?. proc. auto. qed.

lemma set_chain_addr_op_impl (address : adrs, chain_addr : int):
    set_chain_addr_pre chain_addr => 
        hoare[M(Syscall).__set_chain_addr :
            arg = (address, W32.of_int chain_addr) ==> res = set_chain_addr address chain_addr].
proof. move => ?. proc. auto. qed.

lemma set_hash_addr_op_impl (address : adrs, hash_addr : int):
    set_hash_addr_pre hash_addr =>
        hoare[M(Syscall).__set_hash_addr :
            arg = (address, W32.of_int hash_addr) ==> res = set_hash_addr address hash_addr].
proof. move => ?. proc. auto. qed.

lemma set_ltree_addr_op_impl (address : adrs, ltree_addr : int):
    set_ltree_addr_pre ltree_addr =>
        hoare[M(Syscall).__set_ltree_addr :
            arg = (address, W32.of_int ltree_addr) ==> 
                res = set_ltree_addr address ltree_addr].
proof. move => ?. proc. auto. qed.

lemma set_tree_height_op_impl (address : adrs, tree_height : int):
    tree_height_pre tree_height =>
        hoare[M(Syscall).__set_tree_height :
            arg = (address, W32.of_int tree_height) ==> res = set_tree_height address tree_height].
proof. move => ?. proc. auto. qed.

lemma get_set_tree_height (address : adrs, tree_height : int) :
    tree_height_pre tree_height => 
    get_tree_height (set_tree_height address tree_height) = tree_height.
proof.
rewrite /get_tree_height /set_tree_height /tree_height_pre.
move => ?.
smt.
qed.

lemma set_tree_index_op_impl (address : adrs, tree_index) : 
    set_tree_index_pre tree_index => 
        hoare[M(Syscall).__set_tree_index :
            arg = (address, W32.of_int tree_index) ==> res = set_tree_index address tree_index].
proof. move => ?. proc. auto. qed.

lemma get_set_tree_index (address : adrs, tree_index : int) :
  0 <= tree_index < W32.modulus => (* i.e. tree_index fits in a u32 *)
  get_tree_index (set_tree_index address tree_index) = tree_index.  
proof. rewrite /get_tree_index /set_tree_index. move => ?. smt(get_setE @W32). qed.

lemma set_key_and_mask_op_impl (address : adrs, key_and_mask : int):
    hoare[M(Syscall).__set_key_and_mask :
        arg = (address, W32.of_int key_and_mask) ==> res = set_key_and_mask address key_and_mask].
proof. proc. auto. qed.

op zero_addr : adrs = Array8.init (fun _ => W32.zero). 

lemma zero_addr_op_impl (address : adrs) :
    hoare[M(Syscall)._zero_address : true ==> res = zero_addr].
proof.
proc.
while (0 <= i <= 8 /\ 
      (forall (k : int), 0 <= k < i => (addr.[k] = W32.zero))); auto => /> ; smt(get_setE tP initiE).
qed.

(******************************************************* THASH_ *******************************************************)

op thash_f (address : adrs, _seed : seed, t : nbytes) : nbytes =
    let address = set_key_and_mask address 0 in
    let _key = PRF _seed address in
    let address = set_key_and_mask address 1 in
    let bitmask = PRF _seed address in
    F _key (nbytexor t bitmask).

(***************************************************** PRIMITIVES *****************************************************)

op chain(X : nbytes, i s : int, _seed : seed, address : adrs) : nbytes.

(* Definition of the chain operator for s = 0 *)
axiom chain0 (X : nbytes, i s : int, _seed : nbytes, address : adrs) : 
    s = 0 => chain X i s _seed address = X.

axiom chainS (X : nbytes, i s : int, _seed : nbytes, address : adrs) :
    0 < s => chain X i s _seed address =
      let t = chain X i (s - 1) _seed address in 
      let address = set_hash_addr address (i + s - 1) in
      let address = set_key_and_mask address 0 in
      let _key = PRF _seed  address in
      let address = set_key_and_mask address 1 in
      let bitmask = PRF _seed address in
      let t = F _key (nbytexor t bitmask) in
          t.

lemma chain_ll : islossless Chain.chain
  by proc; while (true) (s - chain_count); by auto => /#.

lemma chain_imp_fun (_X : nbytes, _i _s : int, __seed : nbytes, _address : adrs) : 
  chain_pre _X _i _s __seed _address =>
  hoare [ Chain.chain : 
          arg = (_X, _i, _s, __seed, _address) ==>
             res = chain _X _i _s __seed _address].
proof. 
move => pre_cond.
proc => /=.
while(_X = X /\ _i = i /\ _s = s /\ __seed = _seed /\ 
      (forall (k : int), 0 <= k < 6 => _address.[k] = address.[k]) /\ 
      t = chain _X _i chain_count _seed _address /\
      0 <= chain_count <= s); last by auto; smt(chain0).
auto => /> &hr *.
do split; move => *; 1,3,4: by smt(Array8.set_eqiE Array8.set_neqiE).
by rewrite (chainS _ _ (chain_count{hr} + 1) _ _) 1:/# /=;
   congr; congr => /=; [ | congr];
   apply tP => i  ib;
   case (i <> 7); smt(Array8.set_eqiE Array8.set_neqiE).
qed.

(******************************************************************************)

module Checksum = {
  (* part of WOTS *)
  proc checksum (m : W32.t list) : W32.t = {
    var i : int <- 0;
    var m_i : W32.t <- witness;
    var checksum : int <- 0;

    while (i < len1) {
      m_i <- nth witness m i;
      checksum <- checksum + (w - 1) - (W32.to_uint m_i);
      i <- i + 1;
    }

    return (W32.of_int checksum);
  }
}.

(******************************************************************************)


op from_int_list (x : int list) : byte list = map W8.of_int x.

(******************************************************************************)

(* ------------------------------- ISLOSSLESS ------------------------------- *)
