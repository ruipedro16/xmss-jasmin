pragma Goals : printall.

require import AllCore List RealExp IntDiv.
from Jasmin require import JModel.

require import XMSS_IMPL.
require import Address Notation Hash Primitives Params Parameters Utils Util.
require import Correctness_Mem.

require import Array8 Array32 Array64 Array96 Array128.
(*---*) import NBytes.

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

require import Types.

op H (pad a b : nbytes) : nbytes = Hash (pad ++ a ++ b).
op rand_hash_padding : W64.t = W64.one.

module RandHash = {
proc rand_hash (_left _right : nbytes, _seed : nbytes, address : adrs) : nbytes * adrs = { 
  var padding : W8.t list;
  var key : W8.t list;
  var bitmask_0, bitmask_1 : nbytes;
  var buf : W8.t list;
  var addr_bytes : W8.t list;

  padding <@ Util.w64_to_bytes (rand_hash_padding, padding_len);

  address <- set_key_and_mask address 0;
  addr_bytes <- addr_to_bytes address;
  key <@ Hash.prf (addr_bytes, _seed);

  address <- set_key_and_mask address 1;
  addr_bytes <- addr_to_bytes address;
  bitmask_0 <@ Hash.prf (addr_bytes,  _seed);

  address <- set_key_and_mask address 2;
  addr_bytes <- addr_to_bytes address;
  bitmask_1 <@ Hash.prf (addr_bytes,  _seed);

  buf <- (nbytexor _left bitmask_0) ++ (nbytexor _right bitmask_1);
  
  return (H padding key buf, address);
  }
}.


op merge_nbytes_to_array (a b : nbytes) : W8.t Array64.t = 
  Array64.init (fun i => if 0 <= i < 32 then nth witness a i else nth witness b (i - 32)).

lemma rand_hash_correct (i0 i1: nbytes, _pub_seed : W8.t Array32.t, _in : W8.t Array64.t, a : W32.t Array8.t) :
    padding_len = XMSS_PADDING_LEN /\ 
    prf_padding_val = XMSS_HASH_PADDING_PRF /\
    padding_len = XMSS_PADDING_LEN =>
    equiv [
      M(Syscall).__thash_h ~ RandHash.rand_hash :
      arg{1}.`2 = (merge_nbytes_to_array i0 i1) /\
      arg{1}.`3 = _pub_seed /\
      arg{1}.`4 = a /\
      arg{2} = (i0, i1, to_list _pub_seed, a)
      ==>
      to_list res{1}.`1 = res{2}.`1 /\
      res{1}.`2 = res{2}.`2
    ].
proof.
move => *.
proc; auto => />.
conseq (: 
  (forall (k : int), 0 <= k < 32 => in_0{1}.[k] = nth witness _left{2} k) /\
  (forall (k : int), 0 <= k < 32 => in_0{1}.[32 + k] = nth witness _right{2} k) /\
  _seed{2} = to_list pub_seed{1} /\ 
  address{2} = addr{1}
  ==> _
); first by auto => />; rewrite /merge_nbytes_to_array; smt(@List @Array64).
seq 3 0 : (#pre); 1:auto.
seq 1 1 : (#pre /\ padding{2} = to_list aux{1}); first by call {1} (ull_to_bytes_correct W64.one); auto => /> /#.  
swap {1} [2..3] -1. 
seq 2 2 : (#pre /\ addr_bytes{2} = to_list addr_as_bytes{1}).
    + inline {1} M(Syscall).__set_key_and_mask; ecall {1} (addr_to_bytes_correctness addr{1}); auto => /> /#.
seq 1 0 : (
  #pre /\
  forall (k : int), 0 <= k < 32 => buf{1}.[k] = nth witness padding{2} k
); first by auto => /> *; smt(@Array128).
seq 1 1 : (
  (forall (k : int), 0 <= k < 32 => in_0{1}.[k] = nth witness _left{2} k) /\
  (forall (k : int), 0 <= k < 32 => in_0{1}.[32 + k] = nth witness _right{2} k) /\
  _seed{2} = to_list pub_seed{1} /\ 
  address{2} = addr{1} /\
  addr_bytes{2} = to_list addr_as_bytes{1} /\
  key{2} = to_list aux{1} /\

  (* Towards #post *)
  forall (k : int), 0 <= k < 32 => buf{1}.[k] = nth witness padding{2} k
).
    + inline {1} M(Syscall).__prf_ M(Syscall)._prf; wp; sp.
      exists * in_01{1}, key0{1}; elim * => _P1 _P2; call {1} (prf_correctness _P1 _P2); [ smt() | auto => /> ]. 
seq 1 0 : (
    #pre /\
    forall (k : int), 0 <= k < 32 => buf{1}.[32 + k] = nth witness key{2} k
); first by auto => />; smt(@Array128).
seq 2 2 : (#pre).
    + inline {1} M(Syscall).__set_key_and_mask; ecall {1} (addr_to_bytes_correctness addr{1}); auto => /> /#.
seq 2 1 : (
  (forall (k : int), 0 <= k < 32 => in_0{1}.[k] = nth witness _left{2} k) /\
  (forall (k : int), 0 <= k < 32 => in_0{1}.[32 + k] = nth witness _right{2} k) /\
  _seed{2} = to_list pub_seed{1} /\ 
  address{2} = addr{1} /\
  addr_bytes{2} = to_list addr_as_bytes{1} /\
  
  (* Bitmask *)
  (forall (k : int), 0 <= k < 32 => bitmask{1}.[k] = nth witness bitmask_0{2} k) /\

  (* Towards #post *)
  (forall (k : int), 0 <= k < 32 => buf{1}.[k] = nth witness padding{2} k) /\
  (forall (k : int), 0 <= k < 32 => buf{1}.[32 + k] = nth witness key{2} k)
).
    + inline {1} M(Syscall).__prf_ M(Syscall)._prf; wp; sp.
      exists * in_01{1}, key0{1}; elim * => _P1 _P2; call {1} (prf_correctness _P1 _P2); [ smt() | auto => /> *; smt(@Array64) ].
seq 2 2 : (#pre).
    + inline {1} M(Syscall).__set_key_and_mask; ecall {1} (addr_to_bytes_correctness addr{1}); auto => /> /#.
seq 2 1 : (
  #pre /\ 
  (forall (k : int), 0 <= k < 32 => bitmask{1}.[32 + k] = nth witness bitmask_1{2} k)
).
    + inline {1} M(Syscall).__prf_ M(Syscall)._prf; wp; sp.
      exists * in_01{1}, key0{1}; elim * => _P1 _P2; call {1} (prf_correctness _P1 _P2); [ smt() | auto => /> *; smt(@Array64) ].

(* WIP: Maybe use a conseq here to simplify #post *)

(* 
seq 2 0 : (
  #pre /\
  to_list buf{1} = padding{2} ++ nbytexor _left{2} bitmask_0{2} ++ nbytexor _right{2} bitmask_1{2}
).
    + admit.
inline {1} M(Syscall)._core_hash_128; wp; sp.
ecall {1} (hash_128 in_00{1}).
skip => /> &1 &2 *.
rewrite /nbytexor /H.
rewrite /to_list /mkseq -!iotaredE => />.

(* while starts here *)

while (
  0 <= i{1} <= 64 /\
  
)
*)

admit.
qed.
