pragma Goals : printall.

require import AllCore List RealExp IntDiv.
require import BitEncoding.
(*---*) import BitChunking.

from Jasmin require import JModel.

require import RandomBytes XMSS_IMPL Util.

require import Array8 Array32.

require import Params Parameters Address Notation Primitives.
(*---*) import NBytes.

pred valid_ptr (p o : W64.t) = 
  0 <= to_uint o => 
    0 <= to_uint p /\ to_uint (p + o) < W64.modulus.

op BytesToBits (bytes : W8.t list) : bool list = flatten (map W8.w2bits bytes).
op BitsToBytes (bits : bool list) : W8.t list = map W8.bits2w (chunk W8.size bits).
op W64ToBytes (w : W64.t, outlen : int) : W8.t list. (* = BitsToBytes (W64.w2bits w). *)

op addr_to_bytes (a : W32.t Array8.t) : W8.t list = 
  let addr_bits : bool list = flatten (mkseq (fun (i : int) => W32.w2bits a.[i]) 8) in
  BitsToBytes addr_bits.

(** -------------------------------------------------------------------------------------------- **)

lemma ull_to_bytes_correct (x : W64.t) : 
    equiv [M(Syscall).__ull_to_bytes_32 ~ Util.w64_to_bytes :
      arg{1}.`2 = x /\ arg{2} = (x, 32)  ==> res{2} = to_list res{1}].
proof.
proc.
admit.
qed.

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
