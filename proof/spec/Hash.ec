pragma Goals : printall.

require import AllCore List Distr RealExp IntDiv.
require import BitEncoding.
(*---*) import BitChunking.

from Jasmin require import JModel.

require import Primitives.

(*---*) import NBytes.

op Hash : W8.t list -> W8.t list.

op prf_padding_val : W64.t.
op prf_kg_padding_val : W64.t.
op padding_len : int.

module Hash = {
  proc w64_to_bytes (x :W64.t, outlen : int) : W8.t list = { (* TODO: Move to Utils *)
    var r : W8.t list;

    r <- nseq outlen W8.zero;

    return r;
  }

  proc prf (in_0 : W8.t list, key : nbytes) : nbytes = {
    var r : nbytes;
    var padding : W8.t list;
    var buf : W8.t list;

    padding <@ w64_to_bytes (prf_padding_val, padding_len);
    buf <- padding ++ key ++ in_0;

    r <- Hash buf;

    return r;
  }


  proc prf_keygen (in_0 : W8.t list, key : nbytes) : nbytes = {
    var r : nbytes;
    var padding : W8.t list;
    var buf : W8.t list;

    padding <@ w64_to_bytes (prf_kg_padding_val, padding_len);
    buf <- padding ++ key ++ in_0;

    r <- Hash buf;
    
    return r;

  }
}.
