pragma Goals : printall.

require import AllCore List RealExp IntDiv.
from Jasmin require import JModel_x86.

require import Array8 BitEncoding.
(*---*) import BitChunking.

require import Params.

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

op set_layer_addr (address : adrs, layer : int) : adrs = 
    address.[0 <- W32.of_int layer].

op set_tree_addr (address : adrs, tree_address : int) : adrs = 
       address.[1 <- W32.of_int (tree_address %/ 2^32)].[2 <- W32.of_int (tree_address %% 2^32)].

(* Obs: We furthermore assume that the setType() method sets the four words following the type word to zero. *)
op set_type (address : adrs, _type : int) : adrs = 
    address.[3 <- W32.of_int _type].[4 <- W32.zero].[5 <- W32.zero].[6 <- W32.zero].[7 <- W32.zero].

op set_ots_addr (address : adrs, ots_addr : int) : adrs = 
    address.[4 <- W32.of_int ots_addr].

op set_chain_addr (address : adrs, chain_addr : int) : adrs = 
    address.[5 <- W32.of_int chain_addr].

op set_hash_addr (address : adrs, hash_addr : int) : adrs = 
    address.[6 <- W32.of_int hash_addr].

op set_ltree_addr (address : adrs, ltree_addr : int) : adrs = 
    address.[4 <- W32.of_int ltree_addr].

op set_tree_height (address : adrs, tree_height : int) : adrs = 
    address.[5 <- W32.of_int tree_height].
    
op get_tree_height (address : adrs) : int =
  W32.to_uint (address.[5]).

op set_tree_index (address : adrs, tree_index : int) : adrs = 
    address.[6 <- W32.of_int tree_index].

op get_tree_index (address : adrs) : int = to_uint (address.[6]).

op set_key_and_mask (address : adrs, key_and_mask : int) : adrs = 
    address.[7 <- W32.of_int key_and_mask].


(* Isto nao devia estar aqui *)
op BytesToBits (bytes : W8.t list) : bool list = flatten (map W8.w2bits bytes).
op BitsToBytes (bits : bool list) : W8.t list = map W8.bits2w (chunk W8.size bits).

op addr_to_bytes (a : W32.t Array8.t) : nbytes =
  let addr_bytes : W8.t list = 
      flatten (map (fun (w : W32.t) => rev (to_list (W4u8.unpack8 w))) (to_list a)) in
  NBytes.insubd addr_bytes.
