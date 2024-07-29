pragma Goals : printall.

require import AllCore List Distr RealExp IntDiv.
require import BitEncoding.
(*---*) import BitChunking.

from Jasmin require import JModel.

module Utils = {
  proc w64_to_bytes (x : W64.t, outlen : int) = {
    var r : W8.t list;
    
    (* TODO: FIX THIS *)
    r <- nseq outlen W8.zero;
  
    return r;
  } 
}.
