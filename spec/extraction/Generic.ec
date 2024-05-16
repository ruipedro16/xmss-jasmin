require import AllCore List RealExp IntDiv.

from Jasmin require import JModel.

require import Array2 Array3 Array32 Array64 Array67 Array128.

op list_of_array2   ['a] (x : 'a Array2.t)   : 'a list = mkseq (fun (i : int) => x.[i]) 2.
op list_of_array3   ['a] (x : 'a Array3.t)   : 'a list = mkseq (fun (i : int) => x.[i]) 3.
op list_of_array32  ['a] (x : 'a Array32.t)  : 'a list = mkseq (fun (i : int) => x.[i]) 32.
op list_of_array64  ['a] (x : 'a Array64.t)  : 'a list = mkseq (fun (i : int) => x.[i]) 64.
op list_of_array67  ['a] (x : 'a Array67.t)  : 'a list = mkseq (fun (i : int) => x.[i]) 67.
op list_of_array128 ['a] (x : 'a Array128.t) : 'a list = mkseq (fun (i : int) => x.[i]) 128.

op array3_of_list   ['a] (x : 'a list) : 'a Array3.t   = Array3.init   (fun (i : int) => nth witness x i).
op array32_of_list  ['a] (x : 'a list) : 'a Array32.t  = Array32.init  (fun (i : int) => nth witness x i).
op array67_of_list  ['a] (x : 'a list) : 'a Array67.t  = Array67.init  (fun (i : int) => nth witness x i).
op array128_of_list ['a] (x : 'a list) : 'a Array128.t = Array128.init (fun (i : int) => nth witness x i).

module Memcpy = {
  (* This assumes that offset + inlen <= OUTLEN *)
  (* I.e. writing INLEN elements starting at index offset does not write past the end of the array *)
  proc _x_memcpy_u8u8(out : W8.t list, 
                      outlen : int, 
                      offset : W64.t,
                      in_0 : W8.t list, 
                      inlen : int) : W8.t list * W64.t = {
    var i : W64.t <- W64.zero;

    while ((i \ult (W64.of_int inlen))) {
      out <- put out (W64.to_uint offset) in_0.[(W64.to_uint i)];
      i <- (i + (W64.of_int 1));
      offset <- (offset + (W64.of_int 1));
    }

    return (out, offset);
  }
}.

module BaseWGeneric = {
  proc __base_w (output : W32.t list, input : W8.t list) : W32.t list = {

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

    var inlen : W64.t <- W64.of_int (size input);
    var outlen : W64.t <- W64.of_int (size output);

    in_0 <- W64.zero;
    out <- W64.zero;
    bits <- W64.zero;
    consumed <-W64.zero;

    while ((consumed \ult outlen)) {
      if (bits = W64.zero) {
        total <- input.[(W64.to_uint in_0)];
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
