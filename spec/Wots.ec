require import AllCore List Distr RealExp IntDiv.
require (*  *) Subtype.

from Jasmin require import JModel.

require import Notation Address Primitives.

import DList.
import NBytes.

(* sk = u8[XMSS_WOTS_LEN * XMSS_N] = u8[XMSS_WOTS_LEN][XMSS_N] *)
clone import Subtype as LEN_N with 
   type T = nbytes list,
   op P = fun l => size l = len
   rename "T" as "len_n_bytes"
   proof inhabited by (exists (nseq len (nseq n W8.zero));smt(size_nseq ge0_len))
   proof *.


type wots_message = nbytes.
type pkey = len_n_bytes.
type skey = len_n_bytes.
type wots_keypair = pkey * skey.
type wots_signature = len_n_bytes.

module WOTS = {
  proc genSK() : skey = {
    var sk : skey <- nseq len (nseq n W8.zero);
    var sk_i : nbytes;
    var i : int <- 0;


    while (i < len) {
      sk_i <$ DList.dlist W8.dword n;
      sk <- put sk i sk_i;
      i <- i + 1;
    }

    return sk;
  }

  proc genPK(sk : skey, _seed : seed, address : adrs) : pkey = {
    var pk : pkey <- nseq len (nseq n W8.zero);
    var i : int <- 0;
    var pk_i, sk_i : nbytes;

    while (i < len) {
      sk_i <- nth witness sk i;
      pk_i <- chain sk_i 0 (w - 1) _seed address;
      pk <- put pk i pk_i;
      i <- i + 1;
    }

    return pk;
  }

  proc kg(_seed : seed, address : adrs) : wots_keypair = {
    var pk : pkey;
    var sk : skey;

    sk <@ genSK();
    pk <@ genPK(sk, _seed, address);

    return (pk, sk);
  }

  proc sign(M : wots_message, sk : skey, _seed : seed, address : adrs) : wots_signature = {
    var  csum : W32.t;

    var tmp_pk : wots_signature;

    (* TODO: *)

    return tmp_pk;
  }

  proc pkFromSig(M : wots_message, sig : wots_signature, _seed : seed, address : adrs) : pkey = {
    var tmp_pk : pkey;
    
(* TODO *)

    return tmp_pk;
  }

  proc verify(pk : pkey, M : wots_message, sig : wots_signature, _seed : seed, address : adrs) : bool = {
    var tmp_pk : pkey;
    tmp_pk <@ pkFromSig(M, sig, _seed, address);
    return pk = tmp_pk;
  }

}.
op sample_n_bytes : nbytes -> nbytes.
op genSKWots (sk : skey) = map sample_n_bytes sk.

(* Given a list [(a, b)], maps f over  *)
op map1 ['a] (f : nbytes -> nbytes) (xs : (nbytes * 'a) list) =
    with xs = [] => []
    with xs = h::t => (f h.`1, h.`2) :: (map1 f t).

op genPKWots (pk : pkey, sk : skey, _seed : seed, address : adrs) : pkey =
  let keypair = zip pk sk in
  let f : nbytes -> nbytes = fun sk_i => chain sk_i 0 (w-1) _seed address in
  unzip1 (map1 f keypair).

lemma pk_imp_fun (sk : skey, _seed : seed, address : adrs) :
    hoare [WOTS.genPK : arg = (sk, _seed, address) ==> res = genPKWots witness sk _seed address].
proof.
proc.
simplify.
admit. (* FIXME: *)
qed.

op genKeyPairWots (kp : wots_keypair, _seed : seed, address : adrs) : wots_keypair = 
  let sk = genSKWots kp.`2 in
  let pk = genPKWots kp.`1 sk _seed address in
  (pk, sk).

lemma keypair_imp_fun (_seed : seed, address : adrs) :
    hoare [WOTS.kg : arg = (_seed, address) ==> res = genKeyPairWots witness _seed address].
proof.
admit. (* FIXME: *)
qed.
