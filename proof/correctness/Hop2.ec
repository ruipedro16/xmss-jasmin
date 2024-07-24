
pragma Goals : printall.

require import AllCore List RealExp IntDiv.
from Jasmin require import JModel JArray.

require import Params Parameters Address Notation Primitives Wots Generic.
require import RandomBytes XMSS_IMPL XMSS_IMPL_HOP1.

require import Array2 Array3 Array8 Array32 Array64 Array67 Array96 Array128 Array2144.

require import Utils. (* valid ptr predicate & W64ToBytes & addr_to_bytes *)
require import Correctness_Mem. (* memcpy results *)
(*---*) import NBytes.
require import Termination.

require import BitEncoding.
(*---*) import BitChunking.


op padding_len : int.
op padding_val : W64.t.

module Hop2 = {
  proc w64_to_bytes (x : W64.t, outlen : int) = {
    var r : W8.t list;
    
    (* TODO: FIX THIS *)
    r <- nseq outlen W8.zero;
  
    return r;
  } 

  proc prf (in_0 : W8.t list, key : nbytes) : nbytes = {
    var r : nbytes;
    var padding : W8.t list;
    var buf : W8.t list;

    padding <@ w64_to_bytes (padding_val, padding_len);
    buf <- padding ++ key ++ in_0;

    r <- Hash buf;

    return r;
  }

  proc prf_keygen (in_0 : W8.t list, key : nbytes) : nbytes = {
    var r : nbytes;
    var padding : W8.t list;
    var buf : W8.t list;

    padding <@ w64_to_bytes (padding_val, padding_len);
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
    
    padding <@ w64_to_bytes (padding_val, padding_len);
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

   proc pseudorandom_genSK(sk_seed : nbytes, seed : nbytes, address : adrs) : wots_sk * adrs= {
       var sk : wots_sk <- nseq len (nseq n witness);
       var sk_i : nbytes;
       var i : int;
       var addr_bytes : W8.t list;
    
       address <- set_hash_addr address 0;
       address <- set_key_and_mask address 0;

       i <- 0;
       while (i < len) {
       address <- set_chain_addr address i;
       addr_bytes <- addr_to_bytes address;
       sk_i <@ prf_keygen ((seed ++ addr_bytes), sk_seed);
       sk <- put sk i sk_i;
       i <- i + 1;
     }

         return (sk, address);
  }

}.

(*** ***)

lemma ull_to_bytes_correct (x : W64.t) : 
    equiv [M(Syscall).__ull_to_bytes_32 ~ Hop2.w64_to_bytes :
      arg{1}.`2 = x /\ arg{2} = (x, 32)  ==> res{2} = to_list res{1}].
proof.
proc.
admit.
qed.


axiom hash_96 (x : W8.t Array96.t) :
    phoare[M(Syscall).__core_hash_96 : arg.`2 = x ==> to_list res = Hash (to_list x)] = 1%r.

axiom hash_128 (x : W8.t Array128.t) :
    phoare[M(Syscall).__core_hash_128 : arg.`2 = x ==> to_list res = Hash (to_list x)] = 1%r.


lemma prf_hop2 (a b : W8.t Array32.t) :
    padding_val = XMSS_HASH_PADDING_PRF /\ padding_len = XMSS_PADDING_LEN =>
    equiv [
    M(Syscall).__prf ~ Hop2.prf : 
    arg{1}.`2 = a /\ arg{1}.`3 = b /\ arg{2} = (to_list a, to_list b) 
    ==>
    res{2} = to_list res{1}
    ].
proof.
rewrite /XMSS_HASH_PADDING_PRF /XMSS_PADDING_LEN ; move => [p_val p_len].
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


lemma prf_keygen_hop2 (a b : W8.t Array64.t) :
    equiv [
    M(Syscall).__prf_keygen ~ Hop2.prf : 
    arg{1}.`2 = a /\ arg{1}.`2 = b /\ arg{2} = (to_list a, to_list b) 
    ==>
    res{2} = to_list res{1}
    ].
proof.
proc.
seq 9 2 : (buf{2} = to_list buf{1}); last first.
  + inline M(Syscall).__core_hash__128 M(Syscall)._core_hash_128; wp; sp.
    ecall {1} (hash_128 buf{1}); auto => /> /#.
admit.
qed.

(*** ***)

op encode_wots_sk (sk_spec : wots_sk) : W8.t Array2144.t =
    Array2144.of_list witness (flatten sk_spec).

lemma expand_seed_correct (
    _in_seed : W8.t Array32.t, _pub_seed : W8.t Array32.t, _addr : W32.t Array8.t):
    len = XMSS_WOTS_LEN /\ n = XMSS_N =>
    equiv [M(Syscall).__expand_seed ~ Hop2.pseudorandom_genSK :
      arg{1}.`2 = _in_seed /\ 
      arg{1}.`3 = _pub_seed /\
      arg{1}.`4 = _addr /\
      arg{2} = (to_list _in_seed, to_list _pub_seed, _addr) ==>
      res{1}.`1 = encode_wots_sk res{2}.`1 /\ 
      res{1}.`2 = res{2}.`2].
proof.
rewrite /XMSS_WOTS_LEN /XMSS_N; move => [len_val n_val].
proc; auto => />.
conseq (: _ ==>  addr{1} = address{2} /\ forall (k : int), 0 <= k < 2144 => outseeds{1}.[k] = nth witness (flatten sk{2}) k).
  + auto => /> rL rR. rewrite /encode_wots_sk. rewrite /of_list. auto => />. admit.
seq 3 1 : (
  #pre /\
  buf{1} = witness /\
  ith_seed{1} = witness /\
  addr_bytes{1} = witness /\
  size sk{2} = len /\
  size (flatten sk{2}) = 2144
).
    + auto => />. split; smt(@List).
seq 2 2 : ( (* Same as # pre but without addr{1/2} = _addr *)
  inseed{1} = _in_seed /\
  pub_seed{1} = _pub_seed /\
  sk_seed{2} = to_list _in_seed /\
  seed{2} = to_list _pub_seed /\
  ith_seed{1} = witness /\ 
  size sk{2} = len /\ 
  size (flatten sk{2}) = 2144 /\
  addr{1} = address{2}
); first by inline {1}; auto => />.
seq 1 0 : (#pre /\ aux{1} = pub_seed{1}); first by ecall {1} (_x_memcpy_u8u8_post pub_seed{1}); auto => />.
seq 1 0 : (#pre /\ (forall (k : int), 0 <= k < 32 => buf{1}.[k] = pub_seed{1}.[k])); first by auto => /> *; smt(@Array64).
while (
  (* This is from pre *)
  size sk{2} = len /\ size (flatten sk{2}) = 2144 /\
  
  0 <= i{1} <= 67 /\ ={i} /\

  addr{1} = address{2} /\
  addr_bytes{2} = to_list addr_bytes{1} /\
  sk_i{2} = to_list ith_seed{1} /\
  buf{1} = Array64.of_list witness (seed{2} ++ addr_bytes{2}) /\
  
  forall (k : int), 0 <= k < 32 * i{2} => outseeds{1}.[k] = nth witness (flatten sk{2}) k
); last first.
+ auto => /> &1 &2 *. do split.
    - admit.
    - admit.
    - admit.
    - smt(@List @Array2144).
    - by rewrite len_val.
    - move => *. admit.
seq 1 1 : (#pre); first by inline {1}; auto => />.
auto => />.
    + move => &1 &2. move => [#] ?????????????????. move => [#] ?????????????. do split.
        * smt().
        * smt().
        * smt().
        * smt().
        * smt().
        * smt().
        * smt().
        * smt().
        * smt().
        * auto => /> k *. rewrite initE. case (0 <= k && k < 2144); last by smt(). move => ?. 
          case (i{1} * 32 <= k && k < i{1} * 32 + 32); 1,2:by move => ?; smt(@List @Array2144). 
        * smt().
        * smt().
auto => />.
(*
seq 1 0 : (#pre). auto => /> &1 &2 *. apply (eq_from_nth witness). by rewrite !size_to_list. admit.
seq 1 1 : (#pre).
    + ecall {1} (addr_to_bytes_correctness addr{1}). auto => /> &1 &2 *. admit.
*)
admit.
qed.
