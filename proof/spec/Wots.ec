pragma Goals : printall.

require import AllCore List Distr RealExp IntDiv.
require (*--*) Subtype.

from Jasmin require import JModel.

require import Params Notation Address Primitives Hash Params Utils.

import DList.
import NBytes.

require import Array8.

(**********************************************************************************************************************)

clone import Subtype as LEN_N with 
   type T = nbytes list,
   op P = fun l => size l = len
   rename "T" as "len_n_bytes"
   proof inhabited by (exists (nseq len (nseq n W8.zero));smt(size_nseq ge0_len))
   proof *.


clone import Subtype as LEN1 with 
   type T = W8.t list,
   op P = fun l => size l = len1
   rename "T" as "len1_bytes"
   proof inhabited by (exists (nseq len1 W8.zero);smt(size_nseq ge0_len1))
   proof *.

(**********************************************************************************************************************)

type wots_message = nbytes.
type wots_message_base_w = len1_bytes.
type wots_signature = len_n_bytes.
type wots_pk = len_n_bytes.
type wots_sk = len_n_bytes.
type wots_keypair = wots_pk * wots_sk.

(**********************************************************************************************************************)

module WOTS = {
  (* In practise, we generate the private key from a secret seed *)
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
  proc pseudorandom_genSK(sk_seed : nbytes, seed : nbytes, address : adrs) : wots_sk * adrs= {
    var sk : wots_sk <- nseq len (nseq n witness);
    var sk_i : nbytes;
    var addr_bytes : W8.t list;
    var buf : W8.t list;
    var i : int;
    
    address <- set_hash_addr address 0;
    address <- set_key_and_mask address 0;

    i <- 0;
    while (i < len) {
      address <- set_chain_addr address i;
      addr_bytes <- addr_to_bytes address;
      buf <- seed ++ addr_bytes;
      sk_i <@ Hash.prf_keygen (buf, sk_seed);
      sk <- put sk i sk_i;
      i <- i + 1;
    }

    return (sk, address);
  }

  (* The len n-byte strings in the private key each define the start node for one hash chain. The public
  key consists of the end nodes of these hash chains *)
  proc genPK(sk : wots_sk, _seed : seed, address : adrs) : wots_pk * adrs = {
    var pk : wots_pk <- nseq len (nseq n W8.zero);
    var i : int <- 0;
    var pk_i, sk_i : nbytes;

    while (i < len) {
      address <- set_chain_addr address i;
      sk_i <- nth witness sk i;
      (pk_i, address) <@ Chain.chain (sk_i, 0, (w - 1), _seed, address);
      pk <- put pk i pk_i;
      i <- i + 1;
    }

    return (pk, address);
  }

  (* Generates the key from the seed *)
  proc pkGen(sk_seed : nbytes, _seed : seed, address : adrs) : wots_pk * adrs = {
    var pk : wots_pk;
    var wots_skey : wots_sk;
    var i : int <- 0;
    var pk_i, sk_i : nbytes;

    (wots_skey, address) <@ pseudorandom_genSK(sk_seed, _seed, address); (* Generate sk from the secret key *)
    while (i < len) {
      address <- set_chain_addr address i;
      sk_i <- nth witness wots_skey i;
      (pk_i, address) <@ Chain.chain (sk_i, 0, (w - 1), _seed, address);
      pk <- put pk i pk_i;
      i <- i + 1;
    }

    return (pk, address);
  }

  proc kg(sk_seed : nbytes, _seed : seed, address : adrs) : wots_keypair = {
    var pk : wots_pk;
    var sk : wots_sk;

    (sk, address) <@ pseudorandom_genSK(sk_seed, _seed, address);
    (pk, address) <@ genPK(sk, _seed, address);

    return (pk, sk);
  }

  proc checksum (m : int list) : int = {
    var i : int <- 0;
    var m_i : int;
    var checksum : int;

    checksum <- 0;

    while (i < len1) {
      m_i <- nth witness m i;
      checksum <- checksum + (w - 1) - m_i;
      i <- i + 1;
    }

    return checksum;
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
  proc sign(M : wots_message, sk : wots_sk, _seed : seed, address : adrs) : wots_signature * adrs = {
    var csum_32 : W32.t;
    var csum : int;
    var msg : int list;
    var msg_i : int;
    var sk_i : nbytes;
    var len_2_bytes : int;
    var csum_bytes : W8.t list;
    var csum_base_w : int list;
    var sig : wots_signature;
    var sig_i : nbytes;
    var i : int;

    sig <- nseq len (nseq n W8.zero);

    (* Convert message to base w *)
    msg <@ BaseW.base_w(M, len1);

    (* Compute checksum *)
    csum <@ checksum(msg);
    csum_32 <- W32.of_int csum;

    (* Convert checksum to base w *)
    csum_32 <- csum_32 `<<` W8.of_int (8 - ((ceil (len2%r * log2(w%r))) %% 8));
    len_2_bytes <- (ceil ((ceil (len2%r * log2(w%r)))%r / 8%r));

    (* msg = msg || base_w(toByte(csum_32, len_2_bytes), w, len_2); *)
    csum_bytes <- toByte csum_32 len;
    csum_base_w <@ BaseW.base_w(csum_bytes, len_2_bytes);
    msg <- msg ++ csum_base_w;

    i <- 0;
    while (i < len) {
      address <- set_chain_addr address i;
      msg_i <- nth witness msg i;
      sk_i <- nth witness sk i;
      (sig_i, address) <@ Chain.chain (sk_i, 0, msg_i, _seed, address);
      sig <- put sig i sig_i;
      i <- i + 1;
    }

    return (sig, address);
  }

  proc sign_seed (M : wots_message, sk_seed : seed, pub_seed : seed, address : adrs) : wots_signature * adrs = {
    var wots_skey : wots_sk;
    var csum_32 : W32.t;
    var csum : int;
    var msg : int list;
    var msg_i : int;
    var sk_i : nbytes;
    var len_2_bytes : int;
    var csum_bytes : W8.t list;
    var csum_base_w : int list;
    var sig : wots_signature;
    var sig_i : nbytes;
    var i : int;

    sig <- nseq len (nseq n W8.zero);

    (* Generate sk from the secret seed *)
    (wots_skey, address) <@ pseudorandom_genSK(sk_seed, pub_seed, address); 

    (* Convert message to base w *)
    msg <@ BaseW.base_w(M, len1);

    (* Compute checksum *)
    csum <@ checksum(msg);
    csum_32 <- W32.of_int csum;

    (* Convert checksum to base w *)
    csum_32 <- csum_32 `<<` W8.of_int (8 - ((ceil (len2%r * log2(w%r))) %% 8));
    len_2_bytes <- (ceil ((ceil (len2%r * log2(w%r)))%r / 8%r));

    (* msg = msg || base_w(toByte(csum, len_2_bytes), w, len_2); *)
    csum_bytes <- toByte csum_32 len;
    csum_base_w <@ BaseW.base_w(csum_bytes, len_2_bytes);
    msg <- msg ++ csum_base_w;

    i <- 0;
    while (i < len) {
      address <- set_chain_addr address i;
      msg_i <- nth witness msg i;
      sk_i <- nth witness wots_skey i;
      (sig_i, address) <@ Chain.chain (sk_i, 0, msg_i, pub_seed, address);
      sig <- put sig i sig_i;
      i <- i + 1;
    }

    return (sig, address);
  }

  proc pkFromSig(M : wots_message, sig : wots_signature, _seed : seed, address : adrs) : wots_pk * adrs = {
    var tmp_pk : wots_pk <- witness;
    var csum_32 : W32.t;
    var csum : int;
    var msg : int list;
    var len_2_bytes : int;
    var csum_bytes : W8.t list;
    var csum_base_w : int list;
    var i : int;
    var sig_i : nbytes;
    var msg_i : int;
    var pk_i : nbytes;

    (* Convert message to base w *)
    msg <@ BaseW.base_w(M, len1);

    (* Compute checksum *)
    csum <@ checksum(msg);
    csum_32 <- W32.of_int csum;

    (* Convert checksum to base w *)
    csum_32 <- csum_32 `<<` W8.of_int (8 - ((ceil (len2%r * log2(w%r))) %% 8));
    len_2_bytes <- (ceil ((ceil (len2%r * log2(w%r)))%r / 8%r));

    (* msg = msg || base_w(toByte(csum_32, len_2_bytes), w, len_2); *)
    csum_bytes <- toByte csum_32 len;
    csum_base_w <@ BaseW.base_w(csum_bytes, len_2_bytes);
    msg <- msg ++ csum_base_w;
        
    i <- 0;
    while (i < len) {
      address <- set_chain_addr address i;
      msg_i <- nth witness msg i;
      sig_i <- nth witness sig i;
      (pk_i, address) <@ Chain.chain (sig_i, msg_i, (w - 1 - msg_i), _seed, address);
      tmp_pk <- put tmp_pk i pk_i; 
      i <- i + 1;
    }

    return (tmp_pk, address);
  }

  proc verify(pk : wots_pk, M : wots_message, sig : wots_signature, _seed : seed, address : adrs) : bool = {
    var tmp_pk : wots_pk;
    (tmp_pk, address) <@ pkFromSig(M, sig, _seed, address);
    return pk = tmp_pk;
  }
}.

(**********************************************************************************************************************)

(* RFC - p 17
Note that the checksum may reach a maximum integer value of len_1 * (w - 1) * 2^8.
For the parameter sets specified in the RFC, a  32-bit unsigned integer is sufficient 
to hold the checksum.
*)

axiom checksum_max : hoare[WOTS.checksum : true ==> res <= len1 * (w - 1) * 2^8].
axiom checksum_W32 : hoare[WOTS.checksum : true ==> res <= W32.max_uint].

(********************************************************************************************************************)

lemma wots_genSK_ll : islossless WOTS.genSK
    by proc; while (true) (len - i) ; auto => />; [ smt(@Distr @DList @W8) | smt() ].


lemma wots_genSK_prf_ll : islossless WOTS.pseudorandom_genSK.
proof.
proc; wp; sp.
while (true) (len - i) ; auto => />; [ sp; call prf_kg_ll; skip => /> /# | smt() ]. 
qed.

(* TODO: Remove chain_ll lemma from this file => it is already in Properties *)
lemma chain_ll : islossless Chain.chain
  by proc; while (true) (s - chain_count); by auto => /#.

(* TODO: Move this to Generic.ec *)
require import Generic.

lemma spec_base_w_ll : islossless BaseW.base_w.
proof.
proc.
islossless.
while (true) (outlen - consumed) ; by auto => /> /#.
qed.

lemma wots_genPK_ll : islossless WOTS.genPK.
proof.
proc ; islossless.
while (true) (len - i) ; auto => />.
  - call (chain_ll) ; auto => /> /#.
  - smt().
qed.

lemma wots_pkGen_ll : islossless WOTS.pkGen.
proof.
proc.
while (true) (len - i) ; auto => />.
  - call (chain_ll) ; auto => /> /#.
  - call (wots_genSK_prf_ll) ; auto => /#.
qed.

lemma wots_kg_ll : islossless WOTS.kg by proc ; call (wots_genPK_ll) ; call (wots_genSK_prf_ll).

lemma wots_checksum_ll : islossless WOTS.checksum. 
proof.
proc.
while (true) (len1 - i) ; by auto => /> /#.
qed.

lemma wots_sign_ll : islossless WOTS.sign.
proof.
proc.
while (true) (len - i) ; auto => />.
    - wp ; call (chain_ll) ; auto => /> /#.
    - wp ; call (spec_base_w_ll). 
      wp ; call (wots_checksum_ll). 
      wp ; call (spec_base_w_ll). auto => /> /#.
qed.

lemma wots_sign_seed_ll : islossless WOTS.sign_seed.
proof.
proc.
while (true) (len - i) ; auto => />.
  - call chain_ll ; auto => /#.
  - call (spec_base_w_ll) ; auto => />. 
    call (wots_checksum_ll) ; auto => />.
    call (spec_base_w_ll) ; auto => />.
    call (wots_genSK_prf_ll) ; auto => /#.
qed.

lemma wots_pkFromSig_ll : islossless WOTS.pkFromSig.
proof.
proc.
while (true) (len - i) ; auto => />.
  - call (chain_ll) ; auto => /> /#.
  - wp ; call (spec_base_w_ll).
    wp ; call (wots_checksum_ll) ; call (spec_base_w_ll).
    auto => /> /#.
qed.

lemma wots_verify_ll : islossless WOTS.verify by proc ; call (wots_pkFromSig_ll).
