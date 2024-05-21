pragma Goals : printall.

require import AllCore List Distr RealExp IntDiv.
require (*  *) Subtype.

from Jasmin require import JModel.

require import Notation Address Primitives.

import DList.
import NBytes.

(* sk = u8[XMSS_WOTS_LEN * XMSS_N] = u8[XMSS_WOTS_LEN][XMSS_N] *)
(* LEN elements, each with N-byte strings *)
(* XMSS_N is determined by the cryptographic hash functions we use *)
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
op W32_of_W8 (x : W8.t) : W32.t = W32.of_int (W8.to_uint x).

op prf_keygen : nbytes -> nbytes -> nbytes.

module WOTS = {
  proc genSK() : wots_sk = {
    var sk : wots_sk <- nseq len (nseq n W8.zero);
    var sk_i : nbytes;
    var i : int <- 0;

    while (i < len) {
      sk_i <$ DList.dlist W8.dword n; (* Initialize sk[i] with a uniformly random n-byte string *)
      sk <- put sk i sk_i;
      i <- i + 1;
    }

    return sk;
  }
  
  (* 
  Pseudorandom Key Generation [Section 3.1.7. of the RFC]

  During key generation, a uniformly random n-byte string S is
  sampled from a secure source of randomness. This string S is stored
  as private key. The private key elements are computed as sk[i] =
  PRF(S, toByte(i, 32)) whenever needed. Please note that this seed S
  MUST be different from the seed SEED used to randomize the hash
  function calls. Also, this seed S MUST be kept secret. The seed S
  MUST NOT be a low entropy, human-memorable value since private key
  elements are derived from S deterministically and their
  confidentiality is security-critical.
  *)
  proc pseudorandom_genSK(s : nbytes) = {
    var sk : wots_sk <- nseq len (nseq n W8.zero);
    var sk_i : nbytes;
    var key : nbytes;
    var i : int;
    
    i <- 0;
    while (i < n) {
      key <- toByte (W32.of_int i) 32;
      sk_i <- prf_keygen s key;
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

  proc kg(sk_seed : nbytes, _seed : seed, address : adrs) : wots_keypair = {
    var pk : wots_pk;
    var sk : wots_sk;

    sk <@ pseudorandom_genSK(sk_seed);
    pk <@ genPK(sk, _seed, address);

    return (pk, sk);
  }

(*
             +---------------------------------+
             |                                 |
             |           sig_ots[0]            |    n bytes
             |                                 |
             +---------------------------------+
             |                                 |
             ~              ....               ~
             |                                 |
             +---------------------------------+
             |                                 |
             |          sig_ots[len - 1]       |    n bytes
             |                                 |
             +---------------------------------+

                              WOTS+ Signature
*)

  proc sign(m : wots_message, sk : wots_sk, _seed : seed, address : adrs) : wots_signature = {
    var csum : W32.t <- W32.zero;
    var m_i : W8.t;
    var sig : wots_signature <- witness;
    var sig_i : nbytes;
    var sk_i : nbytes;
    var msg_i : int;
    var _m : int list;
    var i : int <- 0;
    var len_2_bytes : int;
    var csum_bytes : byte list;
    var csum_base_w : int list;

    (* Convert message to base w *)
    _m <@ BaseW.base_w(m, len1);
    m <- from_int_list _m;

    (* Compute checksum *)
    while (i < len1) {
      m_i <- nth witness m i;
      csum <- csum + W32.of_int(w - 1) - (W32_of_W8 m_i);
      i <- i + 1;
    }

    (* Convert checksum to base w *)
    csum <- csum `<<` W8.of_int (8 - ((ceil (len2%r * log2(w%r))) %% 8));
    len_2_bytes <- (ceil ((ceil (len2%r * log2(w%r)))%r / 8%r));

    (* msg = msg || base_w(toByte(csum, len_2_bytes), w, len_2); *)
    csum_bytes <- toByte csum len;
    csum_base_w <@ BaseW.base_w(csum_bytes, len_2_bytes);
    m <- m ++ (from_int_list csum_base_w);

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


  (* Note: XMSS uses WOTS_pkFromSig to compute a public key value and
     delays the comparison to a later point. *)
  proc pkFromSig(m : wots_message, sig : wots_signature, _seed : seed, address : adrs) : wots_pk = {
    var tmp_pk : wots_pk <- witness;
    var csum : W32.t <- W32.zero;
    var pk_i : nbytes;
    var m_i : W8.t;
    var _m : int list;
    var i : int <- 0;
    var len_2_bytes : int;
    var sig_i : nbytes;
    var msg_i : int;
    var csum_bytes : byte list;
    var csum_base_w : int list;

    (* Convert message to base w *)
    _m <@ BaseW.base_w(m, len1);
    m <- from_int_list _m;

    (* Compute checksum *)
    while (i < len1) {
      m_i <- nth witness m i;
      csum <- csum + W32.of_int(w - 1) - (W32_of_W8 m_i);
      i <- i + 1;
    }

    (* Convert checksum to base w *)
    csum <- csum `<<` W8.of_int (8 - ((ceil (len2%r * log2(w%r))) %% 8));
    len_2_bytes <- (ceil ((ceil (len2%r * log2(w%r)))%r / 8%r));

    (* msg = msg || base_w(toByte(csum, len_2_bytes), w, len_2); *)
    csum_bytes <- toByte csum len;
    csum_base_w <@ BaseW.base_w(csum_bytes, len_2_bytes);
    m <- m ++ (from_int_list csum_base_w);

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

(* RFC - p 17
Note that the checksum may reach a maximum integer value of len_1 * (w - 1) * 2^8 
and therefore depends on the parameters n and w.


For the parameter sets specified in the RFC, a  32-bit unsigned integer is sufficient 
to hold the checksum
 *)
pred wots_checksum_pred (checksum : W32.t) =
  W32.to_uint checksum <= len1 * (w -2^8).

(* ??? *)
axiom wots_pseudorandom_keygen (s : nbytes) : 
    equiv[WOTS.genSK ~ WOTS.pseudorandom_genSK : true ==> true].

