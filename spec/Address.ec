pragma Goals : printall.

require import AllCore List RealExp IntDiv.
require import WArray32.

from Jasmin require import JModel_x86.

require import Array8.

require import Notation Parameters.

(************************************** EXTRACTION ********************************************************************)
(* FIXME: REMOVE THIS FROM HERE *)

module M = {
  proc _zero_address (addr:W32.t Array8.t) : W32.t Array8.t = {
    var aux: int;
    
    var i:int;
    
    i <- 0;
    while (i < 8) {
      addr.[i] <- (W32.of_int 0);
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

type adrs = W32.t Array8.t.

type addr_type = [ ADDR_TYPE_OTS | ADDR_TYPE_LTREE | ADDR_TYPE_HASHTREE ].

op addr_type_to_int (_type : addr_type) : int = 
    with _type = ADDR_TYPE_OTS      => 0
    with _type = ADDR_TYPE_LTREE    => 1    
    with _type = ADDR_TYPE_HASHTREE => 2.

op int_to_addr_type : int -> addr_type.
axiom int_to_addr_type_0 (_type : int) : _type = 0 => int_to_addr_type _type = ADDR_TYPE_OTS.
axiom int_to_addr_type_1 (_type : int) : _type = 1 => int_to_addr_type _type = ADDR_TYPE_LTREE.
axiom int_to_addr_type_2 (_type : int) : _type = 2 => int_to_addr_type _type = ADDR_TYPE_HASHTREE.

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

pred set_tree_addr_pre (tree_address : int) = 0 <= tree_address.
op set_tree_addr (address : adrs, tree_address : int) : adrs = 
    let t : W32.t = truncateu32 ((SHR_64 (W64.of_int tree_address) (W8.of_int 32)).`6) in
       address.[1 <- t].[2 <- (truncateu32 (W64.of_int tree_address))].

pred set_type_pre (_type : int) = 0 <= _type <= 2.
op set_type (address : adrs, _type : int) : adrs = 
    address.[3 <- W32.of_int _type].

(* TODO: Add Precondition *)
op set_ots_addr (address : adrs, ots_addr : int) : adrs = 
    address.[4 <- W32.of_int ots_addr].

(* TODO: Add Precondition *)
op set_chain_addr (address : adrs, chain_addr : int) : adrs = 
    address.[5 <- W32.of_int chain_addr].

(* TODO: Add Precondition *)
op set_hash_addr (address : adrs, hash_addr : int) : adrs = 
    address.[6 <- W32.of_int hash_addr].

(* TODO: Add Precondition *)
op set_ltree_addr (address : adrs, ltree_addr : int) : adrs = 
    address.[4 <- W32.of_int ltree_addr].

pred tree_height_pre (tree_height : int) = 0 <= tree_height <= XMSS_TREE_HEIGHT. 
op set_tree_height (address : adrs, tree_height : int) : adrs = 
    address.[5 <- W32.of_int tree_height].
op get_tree_height (address : adrs) : int =
  W32.to_uint (address.[5]).

(* TODO: Add Precondition *)
op set_tree_index (address : adrs, tree_index : int) : adrs = 
    address.[6 <- W32.of_int tree_index].

op get_tree_index (address : adrs) : int = to_uint (address.[6]).

op set_key_and_mask (address : adrs, key_and_mask : int) : adrs = 
    address.[7 <- W32.of_int key_and_mask].

