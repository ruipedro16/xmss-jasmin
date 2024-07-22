
pragma Goals : printall.

require import AllCore List RealExp IntDiv.
from Jasmin require import JModel JArray.

require import Params Parameters Address Notation Primitives Wots Generic.
require import RandomBytes XMSS_IMPL XMSS_IMPL_HOP1.

require import Array2 Array3 Array8 Array32 Array67 Array2144.

require import Utils. (* valid ptr predicate & addr_to_bytes *)
require import Correctness_Mem. (* memcpy results *)
(*---*) import NBytes.
require import Termination.


op padding_len : int.
op prf_padding_val : W8.t.
op prf_kg_padding_val : W8.t.

module Hop2 = {
  proc prf (in_0 : W8.t list, key : nbytes) : nbytes = {
    var r : nbytes;
    var padding : W8.t list;
    var buf : W8.t list;

    padding <- nseq padding_len prf_padding_val;
    buf <- padding ++ key ++ in_0;

    r <- Hash buf;

    return r;
  }

  proc prf_keygen (in_0 : W8.t list, key : nbytes) : nbytes = {
    var r : nbytes;
    var padding : W8.t list;
    var buf : W8.t list;

    padding <- nseq padding_len prf_kg_padding_val;
    buf <- padding ++ key ++ in_0;

    r <- Hash buf;
    
    return r;

  }
  
  proc thash_f (out : nbytes, seed : nbytes, address : adrs) : nbytes * adrs = {
    var padding : W8.t list;
    var addr_bytes : W8.t list;
    var u : nbytes;
    var bitmask : nbytes;
    var buf : W8.t list;
    var i : int;
    var t : W8.t;
    
    padding <- nseq padding_len prf_padding_val;
    addr_bytes <- addr_to_bytes address;
    u <@ prf (addr_bytes, seed);

    address <- set_key_and_mask address 1;
    addr_bytes <- addr_to_bytes address;
    
    bitmask <@ prf (addr_bytes, seed);

    buf <- padding ++ u ++ bitmask;

    i <- 0;
    while (i < n) {
      t <- nth witness out i;
      t <- (t `^` (nth witness bitmask i));
      buf <- put buf ((32 + 32) + i) t;
      i <- i + 1;
    }

    out <- Hash buf;

    return (out, address);
  } 

  proc chain(X : nbytes, i s : int, _seed : seed, address : adrs) : nbytes * adrs = {
    var t : nbytes <- X;
    var chain_count : int <- 0;
    var _key : key;
    var bitmask : nbytes;
    var addr_bytes : W8.t list;

    while (chain_count < s) {
      address <- set_hash_addr address (i + chain_count);
      address <- set_key_and_mask address 0;

      _key <- PRF _seed address;
      address <- set_key_and_mask address 1;
      
      addr_bytes <- addr_to_bytes address;
      
      bitmask <@ prf(_seed, addr_bytes);
      
      (t, address) <@ thash_f (t, _seed, address);
      
      chain_count <- chain_count + 1;
    }
    
    return (t, address);
   }
}.


lemma prf_hop2 (a b : W8.t Array32.t) :
    equiv [
    M(Syscall).__prf ~ Hop2.prf : 
    arg{1}.`2 = a /\ arg{1}.`2 = b /\ arg{2} = (to_list a, to_list b) 
    ==>
    res{2} = to_list res{1}
    ].
proof.
proc.
admit.
qed.


lemma prf_hop2 (a b : W8.t Array32.t) :
    equiv [
    M(Syscall).__prf ~ Hop2.prf : 
    arg{1}.`2 = a /\ arg{1}.`2 = b /\ arg{2} = (to_list a, to_list b) 
    ==>
    res{2} = to_list res{1}
    ].
proof.
proc.
admit.
qed.
