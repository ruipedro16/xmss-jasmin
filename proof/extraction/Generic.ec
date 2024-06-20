pragma Goals : printall.

require import AllCore List RealExp IntDiv.

from Jasmin require import JModel.

require import Array64.

module Memcpy = {
  (* This assumes that offset + inlen <= OUTLEN *)
  (* I.e. writing INLEN elements starting at index offset does not write past the end of the array *)
  proc _x_memcpy_u8u8(out : W8.t list, 
                      in_0 : W8.t list) : W8.t list = {
    var i : W64.t <- W64.zero;

    while ((i \ult (W64.of_int (size in_0)))) {
      out <- put out (W64.to_uint i) (nth witness in_0 (W64.to_uint i));
      i <- (i + (W64.of_int 1));
    }

    return out;
  }

  proc __memcpy_u8u8_2 (out:W8.t list, in_0:W8.t list, in_offset:W64.t,
                          bytes:W64.t) : W8.t list * W64.t = {

    var i:W64.t;

    i <- (W64.of_int 0);

    while ((i \ult bytes)) {
      out <- put out (W64.to_uint i) (nth witness in_0 (W64.to_uint in_offset));
      i <- (i + (W64.of_int 1));
      in_offset <- (in_offset + (W64.of_int 1));
    }
    return (out, in_offset);
  }
}.

module BaseWGeneric = {
  proc __base_w (output : W32.t list, input : W8.t list) : W32.t list = {
    
    var in_0:W64.t;
    var bits:W64.t;
    var total:W32.t;
    var i:W64.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var  _0:bool;
    
    in_0 <- (W64.of_int 0);
    bits <- (W64.of_int 0);
    total <- (W32.of_int 0);
    i <- (W64.of_int 0);
    
    while ((i \ult (W64.of_int (size output)))) {
      if ((bits = (W64.of_int 0))) {
        total <- (zeroextu32 (nth witness input (W64.to_uint in_0)));
        in_0 <- (in_0 + (W64.of_int 1));
        bits <- (bits + (W64.of_int 8));
      } 
      
      bits <- (bits - (W64.of_int 4));
      (_of_, _cf_, _sf_,  _0, _zf_, total) <- SHR_32 total (truncateu8 bits);
      total <- (total `&` (W32.of_int (16 - 1)));
      output <- put output (W64.to_uint i) total;
      i <- (i + (W64.of_int 1));
    }
    return (output);
  }
}.

module Memset = {
  proc memset_u8 (a : W8.t list, value : W8.t) : W8.t list = {

    var i:W64.t;
    i <- (W64.of_int 0);
    
    while ((i \ult (W64.of_int (size a)))) {
      a <- put a (W64.to_uint i) value;
      i <- (i + (W64.of_int 1));
    }

    return (a);
  }
}.

lemma memset_post (s : W8.t list, v : W8.t) :
    hoare [Memset.memset_u8 : size s <= 128 ==> (* all ((=) v) res *)
    forall (k : int), 0 <= k < size s => nth witness res k = v].
proof.
proc.
wp;
while (#pre /\ 0 <= to_uint i <= to_uint (W64.of_int (size s)) /\ forall (k : int), 0 <= k < to_uint i => nth witness s (to_uint i) = v); auto => />.
- auto => /> * ; do split.
  + smt(@W64).
  + move => ?. rewrite to_uintD_small of_uintK ; admit.
  + admit.
- move => ?. do split.
  + smt(@W64).
  + smt.
  + auto => /> *. admit.
qed.

lemma memset_ll : phoare [ Memset.memset_u8 : 4 <= size a <= 128 ==> true ] = 1%r.
proof.
proc.
sp.
while (#pre /\ 0 <= to_uint i <= size a) ((size a) - (to_uint i)) ; auto => /> *.
- do split. 
  + admit.
  + rewrite size_put. assumption.
  + rewrite size_put. move => ?. assumption.
  + rewrite size_put /#.
  + rewrite size_put. admit.
- split ; [apply size_ge0 | smt()].
qed.
