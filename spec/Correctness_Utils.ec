pragma Goals : printall.

require import AllCore List RealExp IntDiv.
require Subtype. 

from Jasmin require import JModel.

require import XMSS_IMPL.

require import Array32 Array64 Array96 Array128.

abbrev (=/=) (a b : W64.t) = ! (a = b).
abbrev (<)   (a b : W64.t) = a \ult b. 
abbrev (<=)  (a b : W64.t) = a \ule b.
abbrev (>)   (a b : W64.t) = b \ule a.
abbrev (>=)  (a b : W64.t) = a > b \/ a = b. (* TODO: *)

lemma add_1_W64 (x : W64.t) :
    x > W64.zero => x + W64.one > W64.zero by smt(@W64).

(* true if all of the elements of the array and the list are equal *)
(* TODO: How to use abstract Array instead of Array32 *)
pred list_array_eq (x : W8.t Array32.t, y : W8.t list) =
  size y = 32 /\ forall (k : int), 0 <= k < 32 => x.[k] = y.[k].  

lemma array32_list_put (x : W8.t Array32.t, y : W8.t list, t : W8.t, i : int) :
    list_array_eq x y => list_array_eq x.[i <- t] (put y i t).
proof.
rewrite /list_array_eq.
move => H.
split ; [smt(@List) | progress ; smt(@List @Array32)].
qed.
 
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

module Memcpy = {
  (* This assumes that offset + inlen <= OUTLEN *)
  (* I.e. writing INLEN elements starting at index offset does not write past the end of the array *)
  proc _x_memcpy_u8u8(out : W8.t list, 
                      outlen : int, 
                      offset : W64.t,
                      in_0 : W8.t list, 
                      inlen : int) : W8.t list * W64.t = {
    var i : W64.t <- W64.zero;

    while ((i \ult (W64.of_int outlen))) {
      out <- put out (W64.to_uint offset) in_0.[(W64.to_uint i)];
      i <- (i + (W64.of_int 1));
      offset <- (offset + (W64.of_int 1));
    }

    return (out, offset);
  }
}.

lemma memcmpy_32 (out : W8.t Array32.t, offset : W64.t, in_0 : W8.t Array32.t) :
    (* inlen = 32 /\ outlen = 32 *)
    let _out : W8.t list = mkseq (fun i => out.[i]) 32 in
    let _in : W8.t list = mkseq (fun i => in_0.[i]) 32 in
    size _out = 32 /\ size _in = 32 /\ offset = W64.zero  => 
    equiv [M(Syscall).__memcpy_u8u8_32_32 ~ Memcpy._x_memcpy_u8u8 :
      arg{1} = (out, W64.zero, in_0) /\
      arg{2} = (_out, 32, W64.zero, _in, 32) ==> 
    forall (i : int), 0 <= i < 32 => res{1}.`1.[i] = res{2}.`1.[i]].
proof.
move => H1 H2 H3.
proc.
auto => /> *.
smt().
while (
  W64.zero <= i{1} <= W64.of_int 32 /\
  W64.zero <= i{2} <= W64.of_int 32 /\
  ={i, offset} /\
    list_array_eq in_0{1} H2 /\
  forall (k : int), 0 <= k < W64.to_uint offset{1} => out{1}.[(W64.to_uint offset{1}) + k] = out{2}.[W64.to_uint(offset{1}) + k]
).
auto => />.
progress.
smt(add_1_W64).
smt.
smt(add_1_W64).
smt. 
admit. (*???*)
admit. (*???*)
progress.
auto => /> *. 
progress.
smt().
smt(@List @Array32).
admit. (* No assumptions related to out *)
qed.

lemma memcmpy_64 (out : W8.t Array64.t, offset : W64.t, in_0 : W8.t Array64.t) :
    let _out : W8.t list = mkseq (fun i => out.[i]) 64 in
    let _in : W8.t list = mkseq (fun i => in_0.[i]) 64 in
    size _out = 64 /\ size _in = 64 => 
    equiv [M(Syscall)._x_memcpy_u8u8_64_64 ~ Memcpy._x_memcpy_u8u8 :
      arg{1} = (out, offset, in_0) /\
      arg{2} = (_out, 64, offset, _in, 64) ==> 
    mkseq (fun i => res{1}.`1.[i]) 64 = res{2}.`1].
proof.
admit. (* FIXME: TODO: *)
qed.

lemma memcmpy_128_32 (out : W8.t Array128.t, offset : W64.t, in_0 : W8.t Array32.t) :
    let _out : W8.t list = mkseq (fun i => out.[i]) 128 in
    let _in : W8.t list = mkseq (fun i => in_0.[i]) 32 in
    size _out = 128 /\ size _in = 32 => 
    equiv [M(Syscall)._x_memcpy_u8u8_128_32 ~ Memcpy._x_memcpy_u8u8 :
      arg{1} = (out, offset, in_0) /\
      arg{2} = (_out, 128, offset, _in, 32) ==> 
    mkseq (fun i => res{1}.`1.[i]) 128 = res{2}.`1].
proof.
admit. (* FIXME: TODO: *)
qed.

lemma memcmpy_128_64 (out : W8.t Array128.t, offset : W64.t, in_0 : W8.t Array64.t) :
    let _out : W8.t list = mkseq (fun i => out.[i]) 128 in
    let _in : W8.t list = mkseq (fun i => in_0.[i]) 64 in
    size _out = 128 /\ size _in = 64 => 
    equiv [M(Syscall)._x_memcpy_u8u8_128_64 ~ Memcpy._x_memcpy_u8u8 :
      arg{1} = (out, offset, in_0) /\
      arg{2} = (_out, 128, offset, _in, 64) ==> 
    mkseq (fun i => res{1}.`1.[i]) 128 = res{2}.`1].
proof.
admit. (* FIXME: TODO: *)
qed.

lemma memcmpy_96_32 (out : W8.t Array96.t, offset : W64.t, in_0 : W8.t Array32.t) :
    let _out : W8.t list = mkseq (fun i => out.[i]) 96 in
    let _in : W8.t list = mkseq (fun i => in_0.[i]) 32 in
    size _out = 96 /\ size _in = 32 => 
    equiv [M(Syscall)._x_memcpy_u8u8_96_32 ~ Memcpy._x_memcpy_u8u8 :
      arg{1} = (out, offset, in_0) /\
      arg{2} = (_out, 96, offset, _in, 32) ==> 
    mkseq (fun i => res{1}.`1.[i]) 96 = res{2}.`1].
proof.
admit. (* FIXME: TODO: *)
qed.

lemma memcmpy_64_32 (out : W8.t Array64.t, offset : W64.t, in_0 : W8.t Array32.t) :
    let _out : W8.t list = mkseq (fun i => out.[i]) 64 in
    let _in : W8.t list = mkseq (fun i => in_0.[i]) 32 in
    size _out = 64 /\ size _in = 32 => 
    equiv [M(Syscall)._x_memcpy_u8u8_64_32 ~ Memcpy._x_memcpy_u8u8 :
      arg{1} = (out, offset, in_0) /\
      arg{2} = (_out, 64, offset, _in, 32) ==> 
    mkseq (fun i => res{1}.`1.[i]) 64 = res{2}.`1].
proof.
admit. (* FIXME: TODO: *)
qed.



(*********************************************************************************************)
(************************************* MEMSET ************************************************)
(*********************************************************************************************)

op memset (outlen : int, value : W8.t) = nseq outlen value.


(*
__memset_zero_u8_4
__memset_u8_128
*)

