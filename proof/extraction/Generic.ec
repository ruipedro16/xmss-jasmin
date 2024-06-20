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
