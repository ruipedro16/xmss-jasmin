pragma Goals : printall.

require import AllCore List Distr RealExp IntDiv.

from Jasmin require import JModel.

require import Array8.

require import Address.
require import XMSS_IMPL.

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
    tree_height_pre tree_height /\ tree_height < W32.max_uint => 
    get_tree_height (set_tree_height address tree_height) = tree_height.
proof.
rewrite /get_tree_height /set_tree_height /tree_height_pre.
move => ?.
smt(@W32).
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
    set_key_and_mask_pre key_and_mask =>
        hoare[M(Syscall).__set_key_and_mask :
            arg = (address, W32.of_int key_and_mask) ==> res = set_key_and_mask address key_and_mask].
proof. move => ?. proc. auto. qed.

op zero_addr : adrs = Array8.init (fun _ => W32.zero). 

lemma zero_addr_op_impl (address : adrs) :
    hoare[M(Syscall)._zero_address : true ==> res = zero_addr].
proof.
proc.
while (0 <= i <= 8 /\ 
      (forall (k : int), 0 <= k < i => (addr.[k] = W32.zero))); auto => /> ; smt(get_setE tP initiE).
qed.
