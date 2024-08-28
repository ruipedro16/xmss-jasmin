pragma Goals : printall.

require import AllCore List Distr RealExp IntDiv.
require import BitEncoding.
(*---*) import BitChunking.

from Jasmin require import JModel.

require import Types Params Util Utils Address.

import NBytes.

op Hash : W8.t list -> W8.t list.

op prf_padding_val : W64.t.
op prf_kg_padding_val : W64.t.
op F_padding_val : W64.t.
op rand_hash_padding : W64.t = W64.one.

op padding_len : int.
axiom padding_len_ge0 : 0 <= padding_len.

axiom size_hash (x : W8.t list) :  size (Hash x) = n. 

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

  proc rand_hash (_left _right : nbytes, _seed : nbytes, address : adrs) : nbytes * adrs = {
      var padding : W8.t list;
      var key : W8.t list;
      var bitmask_0, bitmask_1 : nbytes;
      var buf, t : W8.t list; 
      var addr_bytes : W8.t list;
      var r : W8.t list;
    
      padding <@ Util.w64_to_bytes (rand_hash_padding, padding_len);

      address <- set_key_and_mask address 0;
      addr_bytes <- addr_to_bytes address;
      key <@ prf (addr_bytes, _seed);

      address <- set_key_and_mask address 1;
      addr_bytes <- addr_to_bytes address;
      bitmask_0 <@ prf (addr_bytes,  _seed);

      address <- set_key_and_mask address 2;
      addr_bytes <- addr_to_bytes address;
      bitmask_1 <@ prf (addr_bytes,  _seed);
    
      t <- nbytexor (_left ++ _right) (bitmask_0 ++ bitmask_1);
      buf <- padding ++ key ++ t;
  
      return (Hash buf, address);
  }
}.


(*---------------------------------------------------------------------------------------------------------*)

lemma prf_ll : islossless Hash.prf
    by proc; wp; call w64_to_bytes_ll; skip; smt(padding_len_ge0).

lemma prf_kg_ll : islossless Hash.prf_keygen
    by proc; wp; call w64_to_bytes_ll; skip; smt(padding_len_ge0).

lemma f_ll : islossless Hash._F 
    by proc; wp; call w64_to_bytes_ll; skip; smt(padding_len_ge0).

lemma rand_hash_ll : islossless Hash.rand_hash
    by proc; wp; do ! (call prf_ll; wp); call w64_to_bytes_ll; skip; smt(padding_len_ge0).

(*---------------------------------------------------------------------------------------------------------*)

lemma _prf_size : hoare [Hash.prf : true ==> size res = n].
proof.
proc; seq 2 : (true); auto => />; smt(size_hash).
qed.

lemma prf_size : phoare [Hash.prf : true ==> size res = n] = 1%r 
    by conseq prf_ll _prf_size => /#.

lemma _prf_keygen_size : hoare [Hash.prf_keygen : true ==> size res = n].
proof.
proc; seq 2 : (true); auto => />; smt(size_hash).
qed.

lemma prf_keygen_size : phoare [Hash.prf_keygen : true ==> size res = n] = 1%r 
    by conseq prf_kg_ll _prf_keygen_size => /#.

lemma _f_size : hoare [Hash._F : true ==> size res = n].
proof.
proc; seq 2 : (true); auto => />; smt(size_hash).
qed.

lemma f_size : phoare [Hash._F : true ==> size res = n] = 1%r
    by conseq f_ll _f_size => /#.

lemma _randhash_size : hoare [Hash.rand_hash : true ==> size res.`1 = n]
    by proc; seq 12 : (true); [ auto => /> | skip => />; by rewrite size_hash ].

lemma randhash_size : phoare [Hash.rand_hash : true ==> size res.`1 = n] = 1%r
    by conseq rand_hash_ll _randhash_size => /#.

(*---------------------------------------------------------------------------------------------------------*)
