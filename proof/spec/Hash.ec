pragma Goals : printall.

require import AllCore List Distr RealExp IntDiv.
require import BitEncoding.
(*---*) import BitChunking.

from Jasmin require import JModel.

require import Types Params Util.

import NBytes.

op Hash : W8.t list -> W8.t list.

op prf_padding_val : W64.t.
op prf_kg_padding_val : W64.t.
op F_padding_val : W64.t.
op padding_len : int.

axiom padding_len_ge0 : 0 <= padding_len.

module Hash = {
  proc prf (in_0 : W8.t list, key : nbytes) : nbytes = {
    var r : nbytes;
    var padding : W8.t list;
    var buf : W8.t list;

    padding <@ Util.w64_to_bytes (prf_padding_val, padding_len);
    buf <- padding ++ key ++ in_0;

    r <- Hash buf;

    return r;
  }


  proc prf_keygen (in_0 : W8.t list, key : nbytes) : nbytes = {
    var r : nbytes;
    var padding : W8.t list;
    var buf : W8.t list;

    padding <@ Util.w64_to_bytes (prf_kg_padding_val, padding_len);
    buf <- padding ++ key ++ in_0;

    r <- Hash buf;
    
    return r;

  }

  (* Here, t is nbytesxor tmp bitmask *)
  proc _F (key t : nbytes) : nbytes = {
    var r : nbytes;
    var buf : W8.t list;
    var padding : W8.t list;

    padding <@ Util.w64_to_bytes (F_padding_val, padding_len);
    buf <- padding ++ key ++ t;

    r <- Hash buf;

    return r;
  }
}.


(*---------------------------------------------------------------------------------------------------------*)

lemma prf_ll : islossless Hash.prf
    by proc; wp; call w64_to_bytes_ll; skip; smt(padding_len_ge0).

lemma prf_kg_ll : islossless Hash.prf_keygen
    by proc; wp; call w64_to_bytes_ll; skip; smt(padding_len_ge0).

lemma f_ll : islossless Hash._F 
    by proc; wp; call w64_to_bytes_ll; skip; smt(padding_len_ge0).
