pragma Goals : printall.

require import AllCore List RealExp IntDiv.

from Jasmin require import JModel.

require import Params Address.

(* prefix of big endian byte representation of a 32-bit word *)
op toByte(x : W32.t, k : int) : W8.t list =  
    rev (mkseq (fun i => nth W8.zero (to_list (W4u8.unpack8 x)) i) k).


(* From the RFC
  A byte string can be considered as a string of base w numbers, i.e.,
  integers in the set {0, ... , w - 1}.
  In base_w(X, w, out_len), the length out_len is REQUIRED to be less than 
  or equal to 8 * len_X / lg(w).
*)
module BaseW = {
  proc base_w(X : W8.t list, outlen : int) : int list = {
    var _in : int <- 0;
    var out : int <- 0;
    var total : W8.t <- W8.zero;
    var bits : int <- 0;
    var consumed : int <- 0;
    var base_w : int list;
    var v : int;

    base_w <- nseq outlen 0;

    while (consumed < outlen) {
      if (bits = 0) {
        total <- nth witness X _in;
        _in <- _in + 1;
        bits <- bits + 8;
      }

      bits <- bits - floor(log2 w%r);
      
      v <- (W8.to_uint ((total `>>` W8.of_int bits) `&` W8.of_int (w - 1)));
      base_w <- put base_w out v;

      out <- out + 1;
      consumed <- consumed + 1;
    }
    
    return base_w;
  }
}.

pred base_w_pre (X : W8.t list, outlen : int) =
  0 <= outlen <= 8 * size X %/ floor (log2 w%r).

pred base_w_post (X : W8.t list, outlen : int, base_w : int list) =
  size base_w = outlen /\
  all (fun x => 0 <= x <= w - 1) base_w.
