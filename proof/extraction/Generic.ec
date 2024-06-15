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

  proc _x_memcpy_u8u8p(out:W8.t list, offset:W64.t, in_0:W64.t,
                          inlen:W64.t) : W8.t list * W64.t = {

    var i:W64.t;

    i <- (W64.of_int 0);

    while ((i \ult inlen)) {
      out <- put out (W64.to_uint offset) (loadW8 Glob.mem (W64.to_uint (in_0 + i)));
      i <- (i + (W64.of_int 1));
      offset <- (offset + (W64.of_int 1));
    }
    return (out, offset);
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
  proc __base_w (output : W32.t list, outlen : W64.t, input : W8.t list) : W32.t list = {

    var in_0:W64.t;
    var out:W64.t;
    var bits:W64.t;
    var consumed:W64.t;
    var total:W8.t;
    var total_32:W32.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var  _0:bool;

    in_0 <- W64.zero;
    out <- W64.zero;
    bits <- W64.zero;
    consumed <-W64.zero;
    total <- W8.zero;

    while ((consumed \ult outlen)) {
      if (bits = W64.zero) {
        total <- nth witness input (W64.to_uint in_0);
        in_0 <- (in_0 + (W64.of_int 1));
        bits <- (bits + (W64.of_int 8));
      }
      
      bits <- (bits - (W64.of_int 4));
      total_32 <- (zeroextu32 total);
      (_of_, _cf_, _sf_,  _0, _zf_, total_32) <- SHR_32 total_32 (truncateu8 bits);
      total_32 <- (total_32 `&` (W32.of_int (16 - 1)));
      output <- put output (W64.to_uint out) total_32; (* output.[(W64.to_uint out)] <- total_32; *)
      out <- (out + (W64.of_int 1));
      consumed <- (consumed + (W64.of_int 1));
    }

    return (output);
  }
}.

module Memset = {
  proc memset_u8 (a:W8.t list, inlen : W64.t, value:W8.t) : W8.t list = {

    var i:W64.t;
    i <- (W64.of_int 0);
    
    while ((i \ult inlen)) {
      a <- put a (W64.to_uint i) value;
      i <- (i + (W64.of_int 1));
    }
    return (a);
  }
}.
