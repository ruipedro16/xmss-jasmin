pragma Goals : printall.

require import AllCore List RealExp IntDiv.
require import BitEncoding.
(*---*) import BitChunking.

from Jasmin require import JModel.

require import RandomBytes XMSS_IMPL XMSS_IMPL_HOP1.

require import Array8 Array32.

require import Params Parameters Address Notation Primitives Wots.
(*---*) import NBytes.

lemma size_nbytes (x : nbytes) : size x = n.
proof.
admit.
qed.

lemma size_wots_sk (sk : wots_sk) : size sk = len.
proof.
admit.
qed.


lemma size_flatten_wots_sk (sk : wots_sk) : size (flatten sk) = len * n.
proof.
rewrite size_flatten.
admit.
qed.

(*** ***)

pred valid_ptr (p o : W64.t) = 
  0 <= to_uint o => 
    0 <= to_uint p /\ to_uint (p + o) < W64.modulus.

op BytesToBits (bytes : W8.t list) : bool list = flatten (map W8.w2bits bytes).
op BitsToBytes (bits : bool list) : W8.t list = map W8.bits2w (chunk W8.size bits).
op W64ToBytes (w : W64.t, outlen : int) : W8.t list. (* = BitsToBytes (W64.w2bits w). *)

op addr_to_bytes (a : W32.t Array8.t) : W8.t list = 
  let addr_bits : bool list = flatten (mkseq (fun (i : int) => W32.w2bits a.[i]) 8) in
  BitsToBytes addr_bits.


lemma addr_to_bytes_correctness (x : W32.t Array8.t) : 
    phoare[M(Syscall).__addr_to_bytes : arg.`2 = x ==> to_list res = addr_to_bytes x] = 1%r.
proof.
proc.
auto => />. 
admit.
qed.

lemma addr_to_bytes_ll : 
    phoare[M(Syscall).__addr_to_bytes : true ==> true] = 1%r.
proof.
proc; inline.
while (true) (8 - i); auto => /> /#.
qed.

(*
lemma addr_to_bytes_correctness (x : W32.t Array8.t) : 
    phoare[M_Hop1(Syscall).__addr_to_bytes :
      arg.`2 = x ==> res = Array32.of_list witness (addr_to_bytes x)] = 1%r.
proof.
conseq (addr_to_bytes_ll) (addr_to_bytes_correctness x).
auto => />.
qed.
*)

lemma addr_to_bytes_hop1 :
    equiv [M(Syscall).__addr_to_bytes ~ M_Hop1(Syscall).__addr_to_bytes : ={arg} ==> ={res}].  
proof. proc ; sim => />. qed.

(*** Hop 1 ***)

lemma addr_to_bytes_hop1_ll : phoare [ M_Hop1(Syscall).__addr_to_bytes : true ==> true] = 1%r.
proof.
proc ; inline.
while (true) (8 - i); auto => /> /#.
qed.

lemma addr_to_bytes_hop1_correctness (x : W32.t Array8.t) : 
    hoare[M_Hop1(Syscall).__addr_to_bytes : arg.`2 = x ==> to_list res = addr_to_bytes x].
proof.
proc.
auto => />. 
admit.
qed.

lemma p_addr_to_bytes_hop1_correctness (x : W32.t Array8.t) : 
    phoare[M_Hop1(Syscall).__addr_to_bytes :
      arg.`2 = x ==> res = Array32.of_list witness (addr_to_bytes x)] = 1%r.
proof.
conseq (addr_to_bytes_hop1_ll) (addr_to_bytes_hop1_correctness x); auto => /> *.
admit.
qed.

