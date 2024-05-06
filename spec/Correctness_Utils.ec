pragma Goals : printall.

require import AllCore List RealExp IntDiv.
require Subtype. 

from Jasmin require import JModel.

require import XMSS_IMPL.

require import Array32 Array64 Array96 Array128.

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
  (* This assumes that offset + outlen <= INLEN *)
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
    let _out : W8.t list = mkseq (fun i => out.[i]) 32 in
    let _in : W8.t list = mkseq (fun i => in_0.[i]) 32 in
    size _out = 32 /\ size _in = 32 => 
    equiv [M(Syscall)._x_memcpy_u8u8_32_32 ~ Memcpy._x_memcpy_u8u8 :
      arg{1} = (out, offset, in_0) /\
      arg{2} = (_out, 32, offset, _in, 32) ==> 
    mkseq (fun i => res{1}.`1.[i]) 32 = res{2}.`1].
proof.
admit. (* FIXME: TODO: *)
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
