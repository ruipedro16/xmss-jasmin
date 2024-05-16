pragma Goals : printall.

require import AllCore List RealExp IntDiv.
require Subtype. 

from Jasmin require import JModel.

require import XMSS_IMPL.

require import Generic.

require import Array. (* abstract ie before cloning *)

require import Array32 Array64 Array96 Array128.

(*
op mkarray : 'a list -> 'a array.
op ofarray : 'a array -> 'a list.
*)

lemma list_array_size_32 (x : W8.t Array32.t) :
    let y : W8.t list = mkseq (fun (i : int) => x.[i]) 32 in
    size y = 32.
proof.
move => y ; smt(@List).
qed.

(* Adding 1 to a positive number yields a positive number *)
lemma add_1_W64 (x : W64.t) :
    x > W64.zero => x + W64.one > W64.zero by smt(@W64).

(* true if all of the elements of the array and the list are equal *)
(* TODO: How to use abstract Array instead of Array32 *)
(* if I write this to work over any array, the following lemma doesnt work 
pred list_array_eq (x : W8.t array, y : W8.t list) =
  size x = size y /\ forall (k : int), 0 <= k < size x => x.[k] = y.[k].  
*)

pred list_array_eq (x : W8.t Array32.t, y : W8.t list) =
  size y = 32 /\ forall (k : int), 0 <= k < 32 => x.[k] = y.[k].

pred list_array_eq_64 (x : W8.t Array64.t, y : W8.t list) =
  size y = 64 /\ forall (k : int), 0 <= k < 64 => x.[k] = y.[k].

lemma array32_list_put (x : W8.t Array32.t, y : W8.t list, t : W8.t, i : int) :
    list_array_eq x y => list_array_eq x.[i <- t] (put y i t).
proof.
rewrite /list_array_eq.
move => H.
split ; [smt(@List) | progress ; smt(@List @Array32)].
qed.

lemma list_array_size_64 (x : W8.t Array64.t) :
    let y : W8.t list = mkseq (fun (i : int) => x.[i]) 64 in
    size y = 64.
proof.
move => y ; smt(@List).
qed.

lemma size_ge0_W64 (x : 'a list) : W64.to_uint(W64.zero) <= size x by smt(size_ge0).

(*********************************************************************************************)
(************************************* MEMCPY ************************************************)
(*********************************************************************************************)

(* We can see all implementations of this functions by running 
  $ grep -nr "proc _x_memcpy_u8u8_" XMSS_IMPL.ec
      which returns
    _x_memcpy_u8u8_32_32
    _x_memcpy_u8u8_128_32
    _x_memcpy_u8u8_128_64
    _x_memcpy_u8u8_96_32
    _x_memcpy_u8u8_64_32
    _x_memcpy_u8u8_64_64

 *)

lemma memcmpy_32 (out : W8.t Array32.t, offset : W64.t, in_0 : W8.t Array32.t) :
    (* inlen = 32 /\ outlen = 32 *)
    let _out : W8.t list = mkseq (fun i => out.[i]) 32 in
    let _in : W8.t list = mkseq (fun i => in_0.[i]) 32 in
    size _out = 32 /\ size _in = 32 /\ offset = W64.zero  => 
    equiv [M(Syscall).__memcpy_u8u8_32_32 ~ Memcpy._x_memcpy_u8u8 :
      arg{1} = (out, W64.zero, in_0) /\
      arg{2} = (_out, 32, W64.zero, _in, 32) ==> 
    forall (i : int), 0 <= i < 32 => out{1}.[i] = out{2}.[i]].
proof.
move => H0 H1 H3.
proc.
auto => /> *.
while (
  inlen{2} = 32 /\
  W64.zero <= i{1} <= W64.of_int 32 /\
  W64.zero <= offset{1} <= W64.of_int 32 /\
  ={i, offset} /\
    list_array_eq in_0{1} H1 /\
  forall (k : int), 0 <= k < W64.to_uint i{1} => out{1}.[k] = out{2}.[k]
).
auto => />.
progress.
smt(add_1_W64).
smt.
auto => /> *. 
progress by smt. 
(* first smt is () *)
qed.

lemma memcmpy_64 (out : W8.t Array64.t, offset : W64.t, in_0 : W8.t Array64.t) :
    (* inlen = 64 /\ outlen = 64 *)
    let _out : W8.t list = mkseq (fun i => out.[i]) 64 in
    let _in : W8.t list = mkseq (fun i => in_0.[i]) 64 in
    size _out = 64 /\ size _in = 64 /\ offset = W64.zero => 
    equiv [M(Syscall).__memcpy_u8u8_64_64 ~ Memcpy._x_memcpy_u8u8 :
      arg{1} = (out, W64.zero, in_0) /\
      arg{2} = (_out, 64, W64.zero, _in, 64) ==> 
    forall (i : int), 0 <= i < 64 => out{1}.[i] = out{2}.[i]].
proof.
move => H0 H1 H2.
proc.
auto => /> *.
while (
  inlen{2} = 64 /\
  W64.zero <= i{1} <= W64.of_int 64 /\
  W64.zero <= offset{1} <= W64.of_int 64 /\
  ={i, offset} /\
    list_array_eq_64 in_0{1} H1 /\
  forall (k : int), 0 <= k < W64.to_uint i{1} => out{1}.[k] = out{2}.[k]
).
auto => /> ; progress.
smt(add_1_W64).
smt. (* Add lemma for this *)
auto => /> * ; progress by smt.
qed.

lemma memcmpy_128_32 (out : W8.t Array128.t, offset : W64.t, in_0 : W8.t Array32.t) :
    (* inlen = 32 /\ outlen = 128 *)
    (* offset + inlen <= outlen   *)
    (* offset <= outlen - inlen   *)
    let _out : W8.t list = mkseq (fun i => out.[i]) 128 in
    let _in : W8.t list = mkseq (fun i => in_0.[i]) 32 in
    let outlen = size _out in
    let inlen = size _in in
    outlen = 128 /\ inlen = 3 /\ 0 <= W64.to_uint offset <= (outlen - inlen) => 
    equiv [M(Syscall).__memcpy_u8u8_128_32 ~ Memcpy._x_memcpy_u8u8 :
      arg{1} = (out, offset, in_0) /\
      arg{2} = (_out, 128, offset, _in, 32) ==> 
    forall (k : int), 0 <= k < 32 => out{1}.[(W64.to_uint offset) + k] = out{2}.[(W64.to_uint offset) + k]].
proof.
move => H0 H1 H2 H3 H4.
proc.
auto => /> *.
while(
    outlen{2} = 128 /\ inlen{2} = 32 /\
    W64.zero <= i{1} <= W64.of_int 32 (* 32 = inlen *) /\
    ={i, offset} /\
    list_array_eq in_0{1} H1 /\ 
    forall (k : int), 0 <= k < W64.to_uint i{1} => out{1}.[(W64.to_uint offset) + k] = out{2}.[(W64.to_uint offset) + k]
).
auto => /> * ; progress.
smt(add_1_W64).
smt.
auto => /> * ; progress.
smt(list_array_size_32).
smt.
qed.

lemma memcmpy_128_64 (out : W8.t Array128.t, offset : W64.t, in_0 : W8.t Array64.t) :
    (* inlen = 64 /\ outlen = 128 *)
    (* offset + inlen <= outlen   *)
    (* offset <= outlen - inlen   *)
    let _out : W8.t list = mkseq (fun i => out.[i]) 128 in
    let _in : W8.t list = mkseq (fun i => in_0.[i]) 64 in
    let outlen = size _out in 
    let inlen = size _in in
    outlen = 128 /\ inlen = 64 /\ 0 <= W64.to_uint offset <= (outlen - inlen) =>
    equiv [M(Syscall).__memcpy_u8u8_128_64 ~ Memcpy._x_memcpy_u8u8 :
      arg{1} = (out, offset, in_0) /\
      arg{2} = (_out, 128, offset, _in, 64) ==> 
    forall (k : int), 0 <= k < 64 => out{1}.[(W64.to_uint offset) + k] = out{2}.[(W64.to_uint offset) + k]].
proof.
move => H0 H1 H2 H3 H4.
proc.
auto => /> *.
while(
    outlen{2} = 128 /\ inlen{2} = 64 /\
    W64.zero <= i{1} <= W64.of_int 64 (* 64 = inlen *) /\
    ={i, offset} /\
    list_array_eq_64 in_0{1} H1 /\ 
    forall (k : int), 0 <= k < W64.to_uint i{1} => out{1}.[(W64.to_uint offset) + k] = out{2}.[(W64.to_uint offset) + k]
).
auto => /> * ; progress.
smt(add_1_W64).
smt.
auto => /> * ; progress.
smt(list_array_size_64).
smt.
qed.

lemma memcmpy_96_32 (out : W8.t Array96.t, offset : W64.t, in_0 : W8.t Array32.t) :
    (* outlen = 96 /\ inlen = 32 *)
    let _out : W8.t list = mkseq (fun i => out.[i]) 96 in
    let _in : W8.t list = mkseq (fun i => in_0.[i]) 32 in
    let outlen = size _out in 
    let inlen = size _in in
    outlen = 96 /\ inlen = 32 /\ 0 <= W64.to_uint offset <= (outlen - inlen) =>
    equiv [M(Syscall).__memcpy_u8u8_96_32 ~ Memcpy._x_memcpy_u8u8 :
      arg{1} = (out, offset, in_0) /\
      arg{2} = (_out, 96, offset, _in, 32) ==> 
    forall (k : int), 0 <= k < 32 => out{1}.[(W64.to_uint offset) + k] = out{2}.[(W64.to_uint offset) + k]].
proof.
move => H0 H1 H2 H3 H4.
proc.
auto => /> *.
while (
  outlen{2} = 96 /\ inlen{2} = 32 /\
  W64.zero <= i{1} <= W64.of_int 32 (* 32 = inlen *) /\
  ={i, offset} /\
  list_array_eq in_0{1} H1 /\ 
  forall (k : int), 0 <= k < W64.to_uint i{1} => out{1}.[(W64.to_uint offset) + k] = out{2}.[(W64.to_uint offset) + k]
).
auto => /> * ; progress.
smt(add_1_W64).
smt.
auto => /> * ; progress.
smt(list_array_size_32).
smt.
qed.

lemma memcmpy_64_32 (out : W8.t Array64.t, offset : W64.t, in_0 : W8.t Array32.t) :
    (* outlen = 64 /\ inlen = 32 *)
    let _out : W8.t list = mkseq (fun i => out.[i]) 64 in
    let _in : W8.t list = mkseq (fun i => in_0.[i]) 32 in
    let outlen = size _out in 
    let inlen = size _in in
    outlen = 64 /\ inlen = 32 /\ 0 <= W64.to_uint offset <= (outlen - inlen) =>
    equiv [M(Syscall).__memcpy_u8u8_64_32 ~ Memcpy._x_memcpy_u8u8 :
      arg{1} = (out, offset, in_0) /\
      arg{2} = (_out, 64, offset, _in, 32) ==> 
    forall (k : int), 0 <= k < 32 => out{1}.[(W64.to_uint offset) + k] = out{2}.[(W64.to_uint offset) + k]].
proof.
move => H0 H1 H2 H3 H4.
proc.
auto => /> *.
while (
  outlen{2} = 64 /\ inlen{2} = 32 /\
  W64.zero <= i{1} <= W64.of_int 32 (* 32 = inlen *) /\
  ={i, offset} /\
  list_array_eq in_0{1} H1 /\ 
  forall (k : int), 0 <= k < W64.to_uint i{1} => out{1}.[(W64.to_uint offset) + k] = out{2}.[(W64.to_uint offset) + k]
).
auto => /> * ; progress.
smt(add_1_W64).
smt.
auto => /> * ; progress.
smt(list_array_size_32).
smt.
qed.
