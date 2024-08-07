pragma Goals : printall.

require import AllCore List Distr RealExp IntDiv.
require import BitEncoding.
(*---*) import BitChunking.

from Jasmin require import JModel.

module Util = {
  proc w64_to_bytes (in_0 : W64.t, outlen : int) = {
    var r : W8.t list <- nseq outlen W8.zero;
    var i : int;
    var t : W8.t;

    i <- outlen - 1;

    while ((- 1) < i) {
      t <- (truncateu8 in_0);            (* Get the lowest 8 bits *)
      r <- put r i t;
      in_0 <- (in_0 `>>` (W8.of_int 8)); (* Shift right by 8 bits *)
      i <- i - 1;                        (* Move to the next byte *)
    }

    return r;
  } 
}.

lemma w64_to_bytes_ll : 
    phoare [Util.w64_to_bytes : 1 < outlen ==> true] = 1%r.
proof.
proc.
admit.
qed.
