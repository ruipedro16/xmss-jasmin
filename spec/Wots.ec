pragma Goals : printall.

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

axiom ge0_len1 : 0 <= len1.
clone import Subtype as LEN1 with 
   type T = byte list,
   op P = fun l => size l = len1
   rename "T" as "len1_bytes"
   proof inhabited by (exists (nseq len1 W8.zero);smt(size_nseq ge0_len1))
   proof *.


type wots_message = nbytes.
type wots_message_base_w = len1_bytes.
type wots_pk = len_n_bytes.
type wots_sk = len_n_bytes.
type wots_keypair = wots_pk * wots_sk.
type wots_signature = len_n_bytes.

op from_int_list (x : int list) : byte list = map W8.of_int x.

module WOTS = {
  proc genSK() : wots_sk = {
    var sk : wots_sk <- nseq len (nseq n W8.zero);
    var sk_i : nbytes;
    var i : int <- 0;

    while (i < len) {
      sk_i <$ DList.dlist W8.dword n;
      sk <- put sk i sk_i;
      i <- i + 1;
    }

    return sk;
  }

  proc genPK(sk : wots_sk, _seed : seed, address : adrs) : wots_pk = {
    var pk : wots_pk <- nseq len (nseq n W8.zero);
    var i : int <- 0;
    var pk_i, sk_i : nbytes;

    while (i < len) {
      address <- set_chain_addr address i;
      sk_i <- nth witness sk i;
      pk_i <@ Chain.chain (sk_i, 0, (w - 1), _seed, address);
      pk <- put pk i pk_i;
      i <- i + 1;
    }

    return pk;
  }

  proc kg(_seed : seed, address : adrs) : wots_keypair = {
    var pk : wots_pk;
    var sk : wots_sk;

    sk <@ genSK();
    pk <@ genPK(sk, _seed, address);

    return (pk, sk);
  }

  proc sign(m : wots_message, sk : wots_sk, _seed : seed, address : adrs) : wots_signature = {
    var csum : W8.t <- W8.zero;
    var m_i : W8.t;
    var sig : wots_signature;
    var sig_i : nbytes;
    var sk_i : nbytes;
    var msg_i : int;
    var _m : int list;
    var i : int <- 0;
    var len_2_bytes : W8.t;

    sig <- witness; (* To remove warning [warning] [Wots.ec:164] these procedures may use uninitialized local variables: - Top.WOTS.sign -> [sig] *)


    (* Convert message to base w *)
    _m <@ BaseW.base_w(m, len1);
    m <- from_int_list _m;

    (* Compute checksum *)
    while (i < len1) {
      m_i <- nth witness m i;
      csum <- csum + W8.of_int(w - 1) - m_i;
      i <- i + 1;
    }

    (* Convert checksum to base w *)
    csum <- csum `<<` W8.of_int (8 - ((ceil (len2%r * log2(w%r))) %% 8));
    len_2_bytes <- W8.of_int (ceil ((ceil (len2%r * log2(w%r)))%r / 8%r));

    (* FIXME: TODO: *)
    (* msg = msg || base_w(toByte(csum, len_2_bytes), w, len_2); *)

    i <- 0;
    while (i < len) {
      address <- set_chain_addr address i;
      sk_i <- nth witness sk i;
      msg_i <- W8.to_uint (nth witness m i);
      sig_i <@ Chain.chain (sk_i, 0, msg_i, _seed, address);
      sig <- put sig i sig_i;
      i <- i + 1;
    }

    return sig;
  }

  proc pkFromSig(m : wots_message, sig : wots_signature, _seed : seed, address : adrs) : wots_pk = {
    var tmp_pk : wots_pk;
    var csum : W8.t <- W8.zero;
    var pk_i : nbytes;
    var m_i : W8.t;
    var _m : int list;
    var i : int <- 0;
    var len_2_bytes : W8.t;
    var sig_i : nbytes;
    var msg_i : int;

    (* To remove this warning: [warning] [Wots.ec:166] these procedures may use uninitialized local variables:
     - Top.WOTS.pkFromSig -> [tmp_pk] *)
    tmp_pk <- witness;

    (* Convert message to base w *)
    _m <@ BaseW.base_w(m, len1);
    m <- from_int_list _m;

    (* Compute checksum *)
    while (i < len1) {
      m_i <- nth witness m i;
      csum <- csum + W8.of_int(w - 1) - m_i;
      i <- i + 1;
    }

    (* Convert checksum to base w *)
    csum <- csum `<<` W8.of_int (8 - ((ceil (len2%r * log2(w%r))) %% 8));
    len_2_bytes <- W8.of_int (ceil ((ceil (len2%r * log2(w%r)))%r / 8%r));

    (* FIXME: TODO: *)
    (* msg = msg || base_w(toByte(csum, len_2_bytes), w, len_2); *)

    i <- 0;
    while (i < len) {
      address <- set_chain_addr address i;
      sig_i <- nth witness sig i;
      msg_i <- W8.to_uint (nth witness m i);
      pk_i <@ Chain.chain (sig_i, msg_i, (w - 1 - msg_i), _seed, address);
      tmp_pk <- put tmp_pk i pk_i; 
      i <- i + 1;
    }

    return tmp_pk;
  }

  proc verify(pk : wots_pk, M : wots_message, sig : wots_signature, _seed : seed, address : adrs) : bool = {
    var tmp_pk : wots_pk;
    tmp_pk <@ pkFromSig(M, sig, _seed, address);
    return pk = tmp_pk;
  }
}.
