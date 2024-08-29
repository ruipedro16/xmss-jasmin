pragma Goals : printall.

require import AllCore List RealExp IntDiv.
require import BitEncoding.
(*---*) import BitChunking.

from Jasmin require import JModel.

require import XMSS_IMPL Util.

require import Array8 Array32 Array64.

require import Types Params Parameters Address Notation.

import NBytes.

(** -------------------------------------------------------------------------------------------- **)

lemma nbyte_xor_cat (a0 a1 b0 b1 : nbytes) (n : int) :
    size a0 = n /\ size a1 = n /\ size b0 = n /\ size b1 = n =>
        (nbytexor a0 b0) ++ (nbytexor a1 b1) = nbytexor (a0 ++ a1) (b0 ++ b1)
          by smt(@List). 

(** -------------------------------------------------------------------------------------------- **)

(* This is used in treehash *)
(* LHS : Spec               *)
(* RHS : EC Jasmin          *)

lemma mod2_eq_and1_w64 (t : W64.t) : to_uint t %% 2 = to_uint (t `&` W64.one). 
proof.
have ->: 2 = 2^1 by smt(). 
rewrite -to_uint_and_mod 1:/#.
do 3! congr.
smt(). 
qed.

(** -------------------------------------------------------------------------------------------- **)

lemma size_nth (x : W8.t list list) (a i : int) :
    0 <= i < size x =>
      (forall (t : W8.t list), t \in x => size t = a) =>
        size (nth witness x i) = a
          by smt(@List).

(** -------------------------------------------------------------------------------------------- **)

(* size a = 32 /\ size b = 32 *)
op merge_nbytes_to_array (a b : nbytes) : W8.t Array64.t = 
  Array64.init (fun i => if 0 <= i < 32 then nth witness a i else nth witness b (i - 32)).

pred valid_ptr (p o : W64.t) = 
  0 <= to_uint o => 
    0 <= to_uint p /\ to_uint (p + o) < W64.modulus.

pred valid_ptr_i (p : W64.t) (o : int) = 
  0 <= o => 
    0 <= to_uint p /\ to_uint (p) + o < W64.modulus.

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
auto.
seq 0 1 : (#pre /\ size r{2} = 32); first by auto => /> ; rewrite size_nseq.
while (
  ={i, in_0} /\
  0 < i{2} <= 32 /\
  forall (k : int), 0 <= k < i{1} => nth witness r{2} k = out{1}.[k]
); last first.
    + admit.
    + admit.
qed.

lemma addr_to_bytes_correctness (x : W32.t Array8.t) : 
    phoare[M(Syscall).__addr_to_bytes : arg.`2 = x ==> to_list res = addr_to_bytes x] = 1%r.
proof.
proc.
auto => />. 
admit.
qed.

lemma addr_to_bytes_ll : 
    phoare[M(Syscall).__addr_to_bytes : true ==> true] = 1%r
        by proc; inline; while (true) (8 - i); auto => /> /#.

