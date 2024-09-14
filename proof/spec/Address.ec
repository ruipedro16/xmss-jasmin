pragma Goals : printall.

require import AllCore List RealExp IntDiv.
from Jasmin require import JModel_x86.

require import Array8 BitEncoding.
(*---*) import BitChunking.


(* require import XMSS_MT_Types XMSS_MT_Notation XMSS_MT_Params. *)

(**********************************************************************************************************************)

type adrs = W32.t Array8.t.
op zero_address : adrs = Array8.init (fun _ => W32.zero).

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
       address.[1 <- W32.of_int (tree_address %/ 2^32)].[2 <- W32.of_int (tree_address %% 2^32)].

pred set_type_pre (_type : int) = 0 <= _type <= 2.
op set_type (address : adrs, _type : int) : adrs = 
    address.[3 <- W32.of_int _type].

pred set_ots_addr_pre (ots_addr : int) = 0 <= ots_addr.
op set_ots_addr (address : adrs, ots_addr : int) : adrs = 
    address.[4 <- W32.of_int ots_addr].

pred set_chain_addr_pre (chain_addr : int) = 0 <= chain_addr.
op set_chain_addr (address : adrs, chain_addr : int) : adrs = 
    address.[5 <- W32.of_int chain_addr].

op set_hash_addr_pre (hash_addr : int) = 0 <= hash_addr.
op set_hash_addr (address : adrs, hash_addr : int) : adrs = 
    address.[6 <- W32.of_int hash_addr].

pred set_ltree_addr_pre (ltree_addr : int) = 0 <= ltree_addr.
op set_ltree_addr (address : adrs, ltree_addr : int) : adrs = 
    address.[4 <- W32.of_int ltree_addr].

pred tree_height_pre (tree_height : int) = 0 <= tree_height. 
op set_tree_height (address : adrs, tree_height : int) : adrs = 
    address.[5 <- W32.of_int tree_height].
op get_tree_height (address : adrs) : int =
  W32.to_uint (address.[5]).

op set_tree_index_pre (tree_index : int) = 0 <= tree_index.
op set_tree_index (address : adrs, tree_index : int) : adrs = 
    address.[6 <- W32.of_int tree_index].

op get_tree_index (address : adrs) : int = to_uint (address.[6]).

pred set_key_and_mask_pre (key_and_mask : int) = 0 <= key_and_mask <= 2.
op set_key_and_mask (address : adrs, key_and_mask : int) : adrs = 
    address.[7 <- W32.of_int key_and_mask].

op BytesToBits (bytes : W8.t list) : bool list = flatten (map W8.w2bits bytes).
op BitsToBytes (bits : bool list) : W8.t list = map W8.bits2w (chunk W8.size bits).

op addr_to_bytes (a : W32.t Array8.t) : W8.t list = 
  let addr_bits : bool list = flatten (mkseq (fun (i : int) => W32.w2bits a.[i]) 8) in
  BitsToBytes addr_bits.
