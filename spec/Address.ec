pragma Goals : printall.

require import AllCore List RealExp IntDiv.
require import WArray32.

from Jasmin require import JModel_x86.

require import Array8.

require import Notation.

(************************************** EXTRACTION ********************************************************************)
(* FIXME: REMOVE THIS FROM HERE *)

module M = {
  proc _zero_address (addr:W32.t Array8.t) : W32.t Array8.t = {
    var aux: int;
    
    var i:int;
    
    aux <- (8 %/ 2);
    i <- 0;
    while (i < aux) {
      addr <-
      Array8.init
      (WArray32.get32 (WArray32.set64 (WArray32.init32 (fun i_0 => (addr).[i_0])) i ((W64.of_int 0))));
      i <- i + 1;
    }
    return (addr);
  }
  
  proc __set_layer_addr (addr:W32.t Array8.t, layer:W32.t) : W32.t Array8.t = {
    
    
    
    addr.[0] <- layer;
    return (addr);
  }
  
  proc __set_tree_addr (addr:W32.t Array8.t, tree:W64.t) : W32.t Array8.t = {
    
    var t:W64.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var  _0:bool;
    
    t <- tree;
    (_of_, _cf_, _sf_,  _0, _zf_, t) <- SHR_64 t (W8.of_int 32);
    addr.[1] <- (truncateu32 t);
    addr.[2] <- (truncateu32 tree);
    return (addr);
  }
  
  proc __set_type (addr:W32.t Array8.t, type_0:W32.t) : W32.t Array8.t = {
    
    
    
    addr.[3] <- type_0;
    return (addr);
  }
  
  proc __set_key_and_mask (addr:W32.t Array8.t, key_and_mask:W32.t) : 
  W32.t Array8.t = {
    
    
    
    addr.[7] <- key_and_mask;
    return (addr);
  }
  
  proc __set_ots_addr (addr:W32.t Array8.t, ots:W32.t) : W32.t Array8.t = {
    
    
    
    addr.[4] <- ots;
    return (addr);
  }
  
  proc __set_chain_addr (addr:W32.t Array8.t, chain:W32.t) : W32.t Array8.t = {
    
    
    
    addr.[5] <- chain;
    return (addr);
  }
  
  proc __set_hash_addr (addr:W32.t Array8.t, hash:W32.t) : W32.t Array8.t = {
    
    
    
    addr.[6] <- hash;
    return (addr);
  }
  
  proc __set_ltree_addr (addr:W32.t Array8.t, ltree:W32.t) : W32.t Array8.t = {
    
    
    
    addr.[4] <- ltree;
    return (addr);
  }
  
  proc __set_tree_height (addr:W32.t Array8.t, tree_height:W32.t) : W32.t Array8.t = {
    
    
    
    addr.[5] <- tree_height;
    return (addr);
  }
  
  proc __set_tree_index (addr:W32.t Array8.t, tree_index:W32.t) : W32.t Array8.t = {
    
    
    
    addr.[6] <- tree_index;
    return (addr);
  }
}.


(**********************************************************************************************************************)

type byte = W8.t.

type adrs = W32.t Array8.t.      (* u32[8] in Jasmin *)

type addr_type = [ ADDR_TYPE_OTS | ADDR_TYPE_LTREE | ADDR_TYPE_HASHTREE ].

op addr_type_to_int (_type : addr_type) : int = 
    with _type = ADDR_TYPE_OTS      => 0
    with _type = ADDR_TYPE_LTREE    => 1    
    with _type = ADDR_TYPE_HASHTREE => 2.

(* 4th-6th positions differ depending on the type of the address *)

(* OTS Hash Address *)
(* +-------------------------+     *)
(* | layer address  (32 bits)| 0   *)
(* +-------------------------+     *)
(* | tree address   (64 bits)| 1,2 *)
(* +-------------------------+     *)
(* | type = 0       (32 bits)| 3   *)  
(* +-------------------------+     *)
(* | OTS address    (32 bits)| 4   *)
(* +-------------------------+     *)
(* | chain address  (32 bits)| 5   *)
(* +-------------------------+     *)
(* | hash address   (32 bits)| 6   *)
(* +-------------------------+     *)
(* | keyAndMask     (32 bits)| 7   *)
(* +-------------------------+     *)

(* L-tree Address *)
(* +-------------------------+     *)
(* | layer address  (32 bits)| 0   *)
(* +-------------------------+     *)
(* | tree address   (64 bits)| 1,2 *)
(* +-------------------------+     *)
(* | type = 1       (32 bits)| 3   *)
(* +-------------------------+     *)
(* | L-tree address (32 bits)| 4   *)
(* +-------------------------+     *)
(* | tree height    (32 bits)| 5   *)
(* +-------------------------+     *)
(* | tree index     (32 bits)| 6   *)
(* +-------------------------+     *)
(* | keyAndMask     (32 bits)| 7   *)
(* +-------------------------+     *)

(* Hash Tree Address *)
(* +-------------------------+     *)
(* | layer address  (32 bits)| 0   *)
(* +-------------------------+     *)
(* | tree address   (64 bits)| 1,2 *)
(* +-------------------------+     *)
(* | type = 2       (32 bits)| 3   *)
(* +-------------------------+     *)
(* | Padding = 0    (32 bits)| 4   *)
(* +-------------------------+     *)
(* | tree height    (32 bits)| 5   *)
(* +-------------------------+     *)
(* | tree index     (32 bits)| 6   *)
(* +-------------------------+     *)
(* | keyAndMask     (32 bits)| 7   *)
(* +-------------------------+     *)


(**********************************************************************************************************************)

(* layer address describes the height of a tree within the multi-tree, starting from height zero *)
(* for trees at the bottom layer.  The tree address describes the position of a tree within a    *)
(* layer of a multi-tree starting with index zero for the leftmost tree.                         *)
pred set_layer_addr_pre (layer : int) = 0 <= layer.
op set_layer_addr (address : adrs, layer : int) : adrs = 
    address.[0 <- W32.of_int layer].

lemma set_layer_addr_op_impl (addr : adrs, layer: int): 
    set_layer_addr_pre layer => 
        hoare[M.__set_layer_addr : 
            arg = (addr, W32.of_int layer) ==> res = set_layer_addr addr layer].
proof.
move => pre_cond.
proc.
wp.
progress.
qed.

pred set_tree_addr_pre (tree_address : int) = 0 <= tree_address.




op set_tree_addr (address : adrs, tree_address : int) : adrs = 
(* 
FIXME: Should use >> instead of SHR_64.`6 but I cant prove it
let t = (W64.of_int tree_address `>>` W8.of_int 32) in
*)
    let t : W32.t = truncateu32 ((SHR_64 (W64.of_int tree_address) (W8.of_int 32)).`6) in
       address.[1 <- t].[2 <- (truncateu32 (W64.of_int tree_address))].

lemma set_tree_addr_op_impl (address : adrs, tree_address : int):
    set_tree_addr_pre tree_address => 
        hoare[M.__set_tree_addr : 
            arg = (address, W64.of_int tree_address) ==> res = set_tree_addr address tree_address].

proof.
move => pre_cond.
proc.
wp.
progress.
qed.

pred set_type_pre (_type : int) = 0 <= _type /\ _type <= 2.
op set_type (address : adrs, _type : int) : adrs = 
    address.[3 <- W32.of_int _type].
lemma set_type_op_impl (address : adrs, _type : int):
    set_type_pre _type =>
        hoare[M.__set_type :
            arg = (address, W32.of_int _type) ==> res = set_type address _type].
proof.
move => pre_cond.
proc.
wp.
progress.
qed.


(* TODO: Add Precondition *)
op set_ots_addr (address : adrs, ots_addr : int) : adrs = 
    address.[4 <- W32.of_int ots_addr].
lemma set_ots_addr_op_impl (address : adrs, ots_addr : int):
    hoare[M.__set_ots_addr :
        arg = (address, W32.of_int ots_addr) ==> res = set_ots_addr address ots_addr].
proof.
proc.
wp.
progress.
qed.


(* TODO: Add Precondition *)
op set_chain_addr (address : adrs, chain_addr : int) : adrs = 
    address.[5 <- W32.of_int chain_addr].
lemma set_chain_addr_op_impl (address : adrs, chain_addr : int):
    hoare[M.__set_chain_addr :
        arg = (address, W32.of_int chain_addr) ==> res = set_chain_addr address chain_addr].
proof.
proc.
wp.
progress.
qed.


(* TODO: Add Precondition *)
op set_hash_addr (address : adrs, hash_addr : int) : adrs = 
    address.[6 <- W32.of_int hash_addr].
lemma set_hash_addr_op_impl (address : adrs, hash_addr : int):
    hoare[M.__set_hash_addr :
        arg = (address, W32.of_int hash_addr) ==> res = set_hash_addr address hash_addr].
proof.
proc.
wp.
progress.
qed.


(* TODO: Add Precondition *)
op set_ltree_addr (address : adrs, ltree_addr : int) : adrs = 
    address.[4 <- W32.of_int ltree_addr].
lemma set_ltree_addr_op_impl (address : adrs, ltree_addr : int):
    hoare[M.__set_ltree_addr :
        arg = (address, W32.of_int ltree_addr) ==> res = set_ltree_addr address ltree_addr].
proof.
proc.
wp.
progress.
qed.


pred set_tree_height_pre (tree_height : int) = 0 <= tree_height. 
op set_tree_height (address : adrs, tree_height : int) : adrs = 
    address.[5 <- W32.of_int tree_height].
lemma set_tree_height_op_impl (address : adrs, tree_height : int):
    set_tree_height_pre tree_height =>
        hoare[M.__set_tree_height :
            arg = (address, W32.of_int tree_height) ==> res = set_tree_height address tree_height].
proof.
move => pre_cond.
proc.
wp.
progress.
qed.


(* TODO: Add Precondition *)
op set_tree_index (address : adrs, tree_index : int) : adrs = 
    address.[6 <- W32.of_int tree_index].
lemma set_tree_index_op_impl (address : adrs, tree_index : int):
    hoare[M.__set_tree_index :
        arg = (address, W32.of_int tree_index) ==> res = set_tree_index address tree_index].
proof.
proc.
wp.
progress.
qed.

op set_key_and_mask (address : adrs, key_and_mask : int) : adrs = 
    address.[7 <- W32.of_int key_and_mask].
lemma set_key_and_mask_op_impl (address : adrs, key_and_mask : int):
    hoare[M.__set_key_and_mask :
        arg = (address, W32.of_int key_and_mask) ==> res = set_key_and_mask address key_and_mask].
proof.
proc.
wp.
progress.
qed.

op zero_addr(address : adrs) : adrs = map (fun _ => W32.zero) address. 
lemma zero_addr_op_impl (address : adrs):
    hoare[M._zero_address : 
        arg = address ==> res = zero_addr address].
proof.
proc.
while (0 <= i <= 4 /\ address = addr).
    - admit. (* FIXME: *)
    - admit. (* FIXME: *)
qed.
