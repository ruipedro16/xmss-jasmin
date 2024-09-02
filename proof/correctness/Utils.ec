pragma Goals : printall.

require import AllCore List RealExp IntDiv.
require import BitEncoding.
(*---*) import BitChunking.

from Jasmin require import JModel.

require import XMSS_IMPL Util.

require import Array8 Array32 Array64 Array320 Array352.
require import Types Params Parameters Address Notation.

(** -------------------------------------------------------------------------------------------- **)

op concatMap (f: 'a -> 'b list) (a: 'a list): 'b list = flatten (map f a).
op W32ofBytes (bytes : W8.t list) : W32.t = W32.bits2w (concatMap W8.w2bits bytes).
op W32toBytes (x : W32.t) : W8.t list = map W8.bits2w (chunk W8.size (W32.w2bits x)).

(** -------------------------------------------------------------------------------------------- **)

lemma set0_res : set0_64_.`6 = W64.zero by rewrite /set0_64_ //.

lemma size_W32toBytes (x : W32.t) : size (W32toBytes x) = 4
    by rewrite /W32toBytes size_map size_chunk 1:// /w2bits size_mkseq //.

(** -------------------------------------------------------------------------------------------- **)

(*** ------------------------ ***)
(*** outlen=320 /\ inlen=352  ***)
(*** ------------------------ ***)

lemma nbytes_copy_320_352_result (ain : W8.t Array352.t, aout : W8.t Array320.t, oin oout : W64.t) :
    0 <= to_uint oout < 320 - 32 /\
    0 <= to_uint oin < 352 - 32 =>
        phoare [
            M(Syscall).__nbytes_copy_offset_320_352 :
            arg = (aout, oout, ain, oin)
            ==>
            forall (k : int), 0 <= k < 32 => res.[(to_uint oout) + k] = ain.[(to_uint oin) + k]
        ] = 1%r.
proof.
simplify => [#] *.
proc; auto.
while (
  offset_out = oout /\
  offset_in = oin /\
  0 <= i <= 32 /\
  forall (k : int), 0 <= k < i => out.[(to_uint offset_out) + k] = in_0.[(to_uint offset_in) + k]
) (32 - i); last by auto => /> /#.
auto => /> &hr *; do split; 1,2,4:smt().
move => k ??. 
rewrite get_setE. 
    + split; [ smt(@W64 pow2_64) | move => ?;  rewrite to_uintD // of_uintK; smt(@IntDiv @W64 pow2_64)].
case (to_uint oout + k = to_uint (oout + (of_int i{hr})%W64)).
    + move => ?; congr; smt(@W64 pow2_64 @IntDiv).
    + move => ?; smt(@W64 pow2_64 @IntDiv @Array320 @Array352).
qed.

(*** ------------------------ ***)
(*** outlen=352 /\ inlen=32   ***)
(*** ------------------------ ***)

lemma nbytes_copy_352_32_result (ain : W8.t Array32.t, aout : W8.t Array352.t, oin oout : W64.t) :
    0 <= to_uint oout < 352 - 32 /\
    0 <= to_uint oin < 32 - 32 =>
        phoare [
            M(Syscall).__nbytes_copy_offset_352_32 :
            arg = (aout, oout, ain, oin)
            ==>
            forall (k : int), 0 <= k < 32 => res.[(to_uint oout) + k] = ain.[(to_uint oin) + k]
        ] = 1%r.
proof.
simplify => [#] *.
proc; auto.
while (
  offset_out = oout /\
  offset_in = oin /\
  0 <= i <= 32 /\
  forall (k : int), 0 <= k < i => out.[(to_uint offset_out) + k] = in_0.[(to_uint offset_in) + k]
) (32 - i); last by auto => /> /#.
auto => /> &hr *; do split; 1,2,4:smt().
move => k ??. 
rewrite get_setE. 
    + split; [ smt(@W64 pow2_64) | move => ?;  rewrite to_uintD // of_uintK; smt(@IntDiv @W64 pow2_64)].
case (to_uint oout + k = to_uint (oout + (of_int i{hr})%W64)).
    + move => ?; congr; smt(@W64 pow2_64 @IntDiv).
    + move => ?; smt(@W64 pow2_64 @IntDiv @Array352 @Array32).
qed.

(*** ------------------------ ***)
(*** outlen=32 /\ inlen=352   ***)
(*** ------------------------ ***)

lemma nbytes_copy_32_352_result (ain : W8.t Array352.t, aout : W8.t Array32.t, oin oout : W64.t) :
    0 <= to_uint oout < 32 - 32 /\
    0 <= to_uint oin < 352 - 32 =>
        phoare [
            M(Syscall).__nbytes_copy_offset_32_352 :
            arg = (aout, oout, ain, oin)
            ==>
            forall (k : int), 0 <= k < 32 => res.[(to_uint oout) + k] = ain.[(to_uint oin) + k]
        ] = 1%r.
proof.
simplify => [#] *.
proc; auto.
while (
  offset_out = oout /\
  offset_in = oin /\
  0 <= i <= 32 /\
  forall (k : int), 0 <= k < i => out.[(to_uint offset_out) + k] = in_0.[(to_uint offset_in) + k]
) (32 - i); last by auto => /> /#.
auto => /> &hr *; do split; 1,2,4:smt().
move => k ??. 
rewrite get_setE. 
    + split; [ smt(@W64 pow2_64) | move => ?;  rewrite to_uintD // of_uintK; smt(@IntDiv @W64 pow2_64)].
case (to_uint oout + k = to_uint (oout + (of_int i{hr})%W64)).
    + move => ?; congr; smt(@W64 pow2_64 @IntDiv).
    + move => ?; smt(@W64 pow2_64 @IntDiv @Array32 @Array352).
qed.

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

