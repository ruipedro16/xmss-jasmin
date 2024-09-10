pragma Goals : printall.

require import AllCore List RealExp IntDiv.
require import BitEncoding.
(*---*) import BitChunking.

from Jasmin require import JModel.

require import XMSS_IMPL Util.

require import Array8 Array32 Array64 Array320 Array352.
require import WArray96.

require import Types Params Parameters Address Notation.

(** -------------------------------------------------------------------------------------------- **)

op concatMap  (f: 'a -> 'b list) (a: 'a list): 'b list = flatten (map f a).
op W32ofBytes (bytes : W8.t list) : W32.t = W32.bits2w (concatMap W8.w2bits bytes).
op W32toBytes (x : W32.t) : W8.t list = map W8.bits2w (chunk W8.size (W32.w2bits x)).

(** -------------------------------------------------------------------------------------------- **)
lemma size_W32toBytes (x : W32.t) : size (W32toBytes x) = 4 
    by rewrite /W32toBytes size_map size_chunk //.

lemma W32toBytes_zero_nth (i : int) :
    0 <= i < 4 => nth witness (W32toBytes W32.zero) i = W8.zero.
proof.
move => H.
rewrite /W32toBytes.
rewrite (nth_map witness).
  + by rewrite size_chunk.
print w2bits. 
have ->: w2bits W32.zero = nseq 32 false.
  + apply (eq_from_nth false); [ by rewrite size_w2bits size_nseq |].
    rewrite size_w2bits => j?.
    rewrite get_w2bits nth_nseq //=.
have ->: chunk 8 (nseq 32 false) = nseq 4 (nseq 8 false).
  + apply (eq_from_nth witness); [by rewrite size_chunk //= !size_nseq /# |].
    rewrite size_chunk //= size_nseq (: 32 %/ 8 = 4) 1:/# => j?.
    rewrite nth_nseq 1:/#.
    rewrite /chunk nth_mkseq; [by rewrite size_nseq (: 32 %/ 8 = 4) 1:/# |].
    auto => />. 
    apply (eq_from_nth witness).
      * rewrite size_take //= size_drop 1:/# !size_nseq. 
        rewrite (: (max 0 32) = 32) 1:/# (: max 0 (32 - 8 * j) = (32 - 8 *j)) 1:/# /#. 
    rewrite size_take //= size_drop 1:/# !size_nseq.      
    rewrite (: (max 0 32) = 32) 1:/# (: max 0 (32 - 8 * j) = (32 - 8 *j)) 1:/#.
    move => i0?.
    rewrite nth_nseq 1:/# nth_take //= 1:/# nth_drop 1,2:/# nth_nseq 1:/# //.
rewrite nth_nseq //.
rewrite /W8.zero.
congr. 
apply (eq_from_nth false).
  + rewrite size_nseq /int2bs size_mkseq //=.
rewrite size_nseq (: max 0 8 = 8) 1:/# => j?.  
rewrite nth_nseq //= /int2bs nth_mkseq //=.
qed.

(** -------------------------------------------------------------------------------------------- **)

lemma get8_nth (x : W8.t list) (i : int) :
    0 <= i < 96 =>
      get8 (WArray96.of_list x) i = nth W8.zero x i.
proof.
move => H.
rewrite /get8 get_of_list; [assumption | trivial].
qed.

(** -------------------------------------------------------------------------------------------- **)

lemma truncate_1_and_63 :
    truncateu8 (W256.one `&` W256.of_int(63)) = W8.one
        by rewrite (: 63 = 2 ^ 6 - 1) 1:/# and_mod //=.

lemma shr_1 (x : W64.t) :
    to_uint (x `>>` W8.one) = to_uint x %/ 2
        by rewrite shr_div (: (to_uint W8.one %% 64) = 1) 1:#smt:(@W64) //=. 

lemma mod2_vals (x : int) :
    x %% 2 = 0 \/ x %% 2 = 1 by smt(). 

lemma foo (x : W64.t):
    to_uint x %% 2 = 1 => W64.of_int (to_uint x %% 2) = W64.one by smt(@W64). 

lemma and_1_mod_2 (x : W64.t):
    x `&` W64.one <> W64.zero <=> to_uint x %% 2 = 1.
proof.
split; rewrite (: 1 = 2 ^ 1 - 1) 1:/# and_mod //=; [smt(foo) |].
move => H.
rewrite foo //= #smt:(@W64). 
qed.

(** -------------------------------------------------------------------------------------------- **)

lemma nseq_nth (x : W8.t list) (i : int) (v : W8.t) :
    x = nseq i v => forall (k : int), 0 <= k < i => nth witness x k = v
        by smt(@List).

(** -------------------------------------------------------------------------------------------- **)

lemma nth_seed_1 (s s0 s1 s2: W8.t list) (i : int) :
    0 <= i < 32 /\ 
    size s0 = 32 /\ size s1 = 32 /\ size s2 = 32 /\ s = s0 ++ s1 ++ s2 =>
       nth witness s1 i = nth witness s (32 + i).
proof.
move => [#] ?? H0 H1 H2 H3.
rewrite H3 nth_cat size_cat H0 H1 ifT 1:/# nth_cat H0 ifF 1:/# //=.
qed.

lemma nth_seed_2 (s s0 s1 s2: W8.t list) (i : int) :
    0 <= i < 32 /\ 
    size s0 = 32 /\ size s1 = 32 /\ size s2 = 32 /\ s = s0 ++ s1 ++ s2 =>
       nth witness s2 i = nth witness s (64 + i).
proof.
move => [#] ?? H0 H1 H2 H3.
rewrite H3 nth_cat size_cat H0 H1 ifF 1:/# //=.
qed.

(** -------------------------------------------------------------------------------------------- **)

lemma mod_eq (q1 q2 : int) (x : int) :
    0 < q1 /\ 0 < q2 /\ q1 < q2 /\ 0 < x < q1 => 
      x %% q1 = x %% q2 by smt(). 

(** -------------------------------------------------------------------------------------------- **)

lemma W64_eq_W32 (x : W64.t) :
    0 <= to_uint x < W32.max_uint =>
      to_uint x = to_uint (W32.of_int (to_uint x)) 
        by move => ?; rewrite of_uintK #smt(@W32 pow2_32). 

(** -------------------------------------------------------------------------------------------- **)

lemma all_put ['a] (x : 'a list) (y : 'a) (p : 'a -> bool) (i : int) :
    p y =>
    (forall (t : 'a), t \in x => p t) => 
    (forall (t : 'a), t \in (put x i y) => p t) by smt(@List).   


lemma all_take ['a] (x : 'a list) (p : 'a -> bool) (i : int) :
    0 <= i < size x =>
    (forall (t : 'a), t \in x => p t) => 
      (forall (u : 'a), u \in take i x => p u) by smt(@List).

(** -------------------------------------------------------------------------------------------- **)

(* TODO: FIXME: Refactor the 32 out of this *)
lemma size_size (x : W8.t list list) :
	(forall (k : int), 0 <= k < size x => size (nth witness x k) = 32) => 
		all (fun (s : W8.t list) => size s = 32) x
                  by rewrite (all_nthP (fun (s : W8.t list) => size s = 32) x).

lemma size_all (x : W8.t list list)  :
  (all (fun (s : W8.t list) => size s = 32) x) =
    (forall (t0 : W8.t list), t0 \in x => 32 = size t0)
      by smt(@List). 

 lemma size_all_r (x : W8.t list list)  :
  (all (fun (s : W8.t list) => size s = 32) x) =
    (forall (t0 : W8.t list), t0 \in x => size t0 = 32)
      by smt(@List). 

(** -------------------------------------------------------------------------------------------- **)

lemma simplify_pow (a b : int) : 
    0 < a /\ 0 < b => 
      a%r ^ b%r = (a ^ b)%r.
proof.
move => [#] ??.
rewrite -RField.fromintXn 1:/# #smt:(@RealExp).
qed.

hint simplify simplify_pow. 

(** -------------------------------------------------------------------------------------------- **)

(* NOTE: This lemma needs to be defined after the previous hint *)
(* This is used a lot in the proofs for wots *)

lemma log2_16 : log2 16%r = 4%r.
proof.
have ->: 16%r = 2%r ^ 4%r by simplify.
rewrite /log2 logK /#.
qed.

lemma ceil_3_2 : ceil (3%r / 2%r) = 2.
proof.
have ? : 1 < ceil (3%r / 2%r) by smt(@Real).
have ? : ceil (3%r / 2%r) <= 2 by smt(@Real).
smt().
qed.

(** -------------------------------------------------------------------------------------------- **)

lemma set0_res : set0_64_.`6 = W64.zero by rewrite /set0_64_ //.

(** -------------------------------------------------------------------------------------------- **)

require import Array4.

lemma memset_zero :
    hoare [ M(Syscall).__memset_zero_u8 : true ==> to_list res = nseq 4 W8.zero].
proof.
proc.
while (
  0 <= to_uint i <= 4 /\
  forall (k : int), 0 <= k < to_uint i => a.[k] = W8.zero
).
    + auto => /> &hr *; do split; 1,2:smt(@W64). 
      move => k??. rewrite get_setE; first by smt(@W64).
      smt(@Array4 @W64).       
    + auto => /> &hr; split; 1:smt(). move => ? j ???. 
      have ->: to_uint j = 4 by smt(@W64 pow2_64).  
      move => H. 
      apply (eq_from_nth witness); first by rewrite size_to_list size_nseq. 
      rewrite size_to_list => *. 
      rewrite get_to_list nth_nseq /#. 
qed.

lemma toByteZero : toByte W32.zero 4 = nseq 4 W8.zero.
proof.
rewrite /toByte.
apply (eq_from_nth W8.zero).
  + rewrite size_take 1:/# size_nseq size_rev size_to_list //.
have ->: size (take 4 (rev (to_list (unpack8 W32.zero)))) = 4.
  + rewrite size_take 1:/# size_rev size_to_list //.
move => i?.
rewrite nth_nseq 1:/# nth_take 1,2:/#.
rewrite nth_rev; first by rewrite size_to_list //.
rewrite size_to_list.

case (i = 0).  
  + move => Hi. rewrite Hi //=.
case (i = 1).
  + move => Hi?. rewrite Hi //=.
case (i = 2).
  + move => Hi??. rewrite Hi //=.
case (i = 3).
  + move => Hi???. rewrite Hi //=.
move => ????. have ->: i = 4 by smt().
smt(). 
qed.

lemma memset_toByte_Zero : 
    hoare [ M(Syscall).__memset_zero_u8 : true ==> to_list res = toByte W32.zero 4 ].
proof.
rewrite /toByte; proc.
while (
  0 <= to_uint i <= 4 /\ 
  (forall (k : int), 0 <= k < to_uint i => a.[k] = W8.zero)
).

    + auto => /> &hr H0 H1 H2 H3; do split; 1,2:smt(@W64 pow2_64).
      move => k??. 
      rewrite get_setE 1:#smt:(@W64 pow2_64).
      smt(@Array4 @W64).  
    + auto => /> &hr; do split; 1:smt(). 
      move => a i ???. 
      have ->: to_uint i = 4 by smt(@W64 pow2_64).
      move => H.
      have ->: to_list a = nseq 4 W8.zero.
         * apply (eq_from_nth witness); [by rewrite size_to_list size_nseq |].
           rewrite size_to_list => j?. rewrite get_to_list H //= nth_nseq //=.
      apply (eq_from_nth witness); [rewrite size_take //= size_nseq size_rev size_to_list //= |].
      rewrite size_nseq (: max 0 4 = 4) 1:/#  => j?.        
      rewrite nth_nseq //= nth_take 1,2:/# nth_rev; [by rewrite size_to_list //= |].
      rewrite size_to_list.
      have ->: nth witness (to_list (unpack8 W32.zero)) (4 - (j + 1)) = 
               (unpack8 W32.zero).[4 - (j+1)] by smt(@List).
      rewrite get_unpack8 1:/# get_zero //=.
qed.

(** -------------------------------------------------------------------------------------------- **)

require import Array132.

(*** ------------------------ ***)
(*** outlen=352 /\ inlen=32  ***)
(*** ------------------------ ***)

lemma nbytes_copy_352_32_result (ain : W8.t Array32.t, aout : W8.t Array352.t, oin oout : W64.t) :
    0 <= to_uint oout < 320 - 32 /\
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
smt().
qed.

(*** ------------------------ ***)
(*** outlen=64 /\ inlen=32  ***)
(*** ------------------------ ***)

lemma nbytes_copy_64_32_result (ain : W8.t Array32.t, aout : W8.t Array64.t) :
        phoare [
            M(Syscall).__nbytes_copy_offset_64_32 :
            arg = (aout, W64.of_int 68, ain, W64.zero)
            ==>
            forall (k : int), 0 <= k < 32 => res.[68 + k] = ain.[k]
        ] = 1%r.
proof.
proc.
while (
  0 <= i <= 32 /\
  forall (k : int), 0 <= k < i => out.[(to_uint offset_out) + k] = in_0.[k]
) (32 - i); last by auto => /> /#.
auto => /> &hr *; do split; 1,2,4:smt().
move => k ??. 
rewrite get_setE. 
    + split; [smt(@W64 pow2_64) |] => ?.
admit.
admit.
qed.

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
    + move => ?; smt(@W64 pow2_64 @IntDiv).
qed.

(*** ------------------------ ***)
(*** outlen=132 /\ inlen=32  ***)
(*** ------------------------ ***)

lemma nbytes_copy_132_32_result (ain : W8.t Array32.t, aout : W8.t Array132.t, oin oout : W64.t) :
    0 <= to_uint oout < 320 - 32 /\
    0 <= to_uint oin < 32 - 32 =>
        phoare [
            M(Syscall).__nbytes_copy_offset_132_32 :
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
smt().
qed.

(*** ------------------------ ***)
(*** outlen=32 /\ inlen=352  ***)
(*** ------------------------ ***)

lemma nbytes_copy_32_352_result (ain : W8.t Array352.t, aout : W8.t Array32.t, oin oout : W64.t) :
    0 <= to_uint oout < 320 - 32 /\
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
    + split. smt(@W64 pow2_64). move => ?.  rewrite to_uintD_small. smt(@W64 pow2_64). admit.
admit.
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

lemma _addr_to_bytes_correctness (x : W32.t Array8.t) : 
    hoare[M(Syscall).__addr_to_bytes : arg.`2 = x ==> to_list res = addr_to_bytes x].
proof.
rewrite /addr_to_bytes /BitsToBytes; proc.
auto => />. 
while (
   0 <= i <= 8
).
admit.
admit.
qed.

lemma addr_to_bytes_ll : islossless M(Syscall).__addr_to_bytes by proc; inline; while (true) (8 - i); auto => /> /#.

lemma addr_to_bytes_correctness (x : W32.t Array8.t) : 
    phoare[M(Syscall).__addr_to_bytes : arg.`2 = x ==> 
      to_list res = addr_to_bytes x] = 1%r.
proof.
proc.
(* conseq addr_to_bytes_ll (_addr_to_bytes_correctness x). *)
admit.
qed.
