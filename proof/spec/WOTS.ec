pragma Goals : printall.

require import AllCore List Distr RealExp IntDiv DList.
from Jasmin require import JModel.

require import Params BaseW Address Hash.

(******************************************************************************)

type key = nbytes.
type seed = nbytes.

(******************************************************************************)

type wots_message = nbytes.
type wots_message_base_w = onebyte.
type wots_signature = len_nbytes.
type wots_pk = len_nbytes.
type wots_sk = len_nbytes.
type wots_keypair = wots_pk * wots_sk.

(******************************************************************************)

clone import Subtype as OTSKeys with 
   type T = wots_sk list,
   op P = fun l => size l = 2^h
   rename "sT" as "wots_ots_keys".

op nbytexor(a b : nbytes) : nbytes = NBytes.insubd (bytexor (val a) (val b)).

module Chain = {
   proc chain(X : nbytes, i s : int, _seed : seed, address : adrs) : nbytes = {
      (*
       *
       * i: start index
       * s: number of steps
       *
       *)
    var t : nbytes <- X;
    var chain_count : int <- 0;
    var _key : key;
    var bitmask : nbytes;
    var addr_bytes : nbytes;

    (* case i + s <= w-1 is precondition *)
    while (chain_count < s) {
     address <- set_hash_addr address (i + chain_count);
     address <- set_key_and_mask address 0;
      
      addr_bytes <- addr_to_bytes address;
     _key <@ Hash.prf(addr_bytes, _seed);
     
     address <- set_key_and_mask address 1;
      
     addr_bytes <- addr_to_bytes address;
     bitmask <@ Hash.prf(addr_bytes, _seed);

     t <@ Hash._F (_key, (nbytexor t bitmask));
     
     chain_count <- chain_count + 1;
    }
    
    return t;
   }
}.

pred chain_pre(X : nbytes, i s : int, _seed : seed, address : adrs) = 
    0 <= s <= w-1.

module WOTS = {
  (* In practise, we generate the private key from a secret seed *)
  proc genSK() : wots_sk = {
    var sk : W8.t list list;
    var sk_i : W8.t list;
    var i : int;

    sk <-(nseq len (nseq n W8.zero));
    i <- 0;

    while (i < len) {
      sk_i <$ DList.dlist W8.dword n; (* Initialize sk[i] with a uniformly random n-byte string *)
      sk <- put sk i sk_i;
      i <- i + 1;
    }

    return insubd (map NBytes.insubd sk);
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
  proc pseudorandom_genSK(sk_seed : nbytes, seed : nbytes, address : adrs) : wots_sk = {
    var sk : nbytes list;
    var sk_i : nbytes;
    var addr_bytes : nbytes;
    var buf : W8.t list;
    var i : int;

    sk <-  nseq len witness;
    
    address <- set_hash_addr address 0;
    address <- set_key_and_mask address 0;

    i <- 0;
    while (i < len) {
      address <- set_chain_addr address i;
      addr_bytes <- addr_to_bytes address;
      sk_i <@ Hash.prf_keygen (val seed ++ val addr_bytes, sk_seed);
      sk <- put sk i sk_i;
      i <- i + 1;
    }

    return insubd sk;
  }

  (* The len n-byte strings in the private key each define the start node for one hash chain. The public
  key consists of the end nodes of these hash chains *)
  proc genPK(sk : wots_sk, _seed : seed, address : adrs) : wots_pk = {
    var pk : nbytes list;
    var i : int;
    var pk_i, sk_i : nbytes;

    pk <- nseq len witness;
    i <- 0;

    while (i < len) {
      address <- set_chain_addr address i;
      sk_i <- nth witness (val sk) i;
      pk_i <@ Chain.chain (sk_i, 0, (w - 1), _seed, address);
      pk <- put pk i pk_i;
      i <- i + 1;
    }

    return insubd pk;
  }

  (* Generates the key from the seed *)
  proc pkGen(sk_seed : nbytes, _seed : seed, address : adrs) : wots_pk  = {
    var pk : nbytes list;
    var wots_skey : wots_sk;
    var i : int;
    var pk_i, sk_i : nbytes;

    pk <- nseq len witness;
    i <- 0;
   

    wots_skey <@ pseudorandom_genSK(sk_seed, _seed, address); (* Generate sk from the secret key *)
    while (i < len) {
      address <- set_chain_addr address i;
      sk_i <- nth witness (val wots_skey) i;
      pk_i <@ Chain.chain (sk_i, 0, (w - 1), _seed, address);
      pk <- put pk i pk_i;
      i <- i + 1;
    }

    return insubd pk;
  }

  proc kg(sk_seed : nbytes, _seed : seed, address : adrs) : wots_keypair = {
    var pk : wots_pk;
    var sk : wots_sk;

    sk <@ pseudorandom_genSK(sk_seed, _seed, address);
    pk <@ genPK(sk, _seed, address);

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

  proc sign(M : wots_message, sk : wots_sk, _seed : seed, address : adrs) : wots_signature = {
    var csum_32 : W32.t;
    var csum : int;
    var msg : int list;
    var msg_i : int;
    var sk_i : nbytes;
    var len_2_bytes : int;
    var csum_bytes : W8.t list;
    var csum_base_w : int list;
    var sig : nbytes list;
    var sig_i : nbytes;
    var i : int;

    sig <- nseq len witness;

    (* Convert message to base w *)
    msg <@ BaseW.base_w(val M, len1);

    (* Compute checksum *)
    csum <@ checksum(msg);
    csum_32 <- W32.of_int csum;

    (* Convert checksum to base w *)
    csum_32 <- csum_32 `<<` W8.of_int (8 - ((ceil (len2%r * log2(w%r))) %% 8));
    len_2_bytes <- (ceil ((ceil (len2%r * log2(w%r)))%r / 8%r));

    (* msg = msg || base_w(toByte(csum_32, len_2_bytes), w, len_2); *)
    csum_bytes <- toByte csum_32 len2;
    csum_base_w <@ BaseW.base_w(csum_bytes, len_2_bytes);
    msg <- msg ++ csum_base_w;

    i <- 0;
    while (i < len) {
      address <- set_chain_addr address i;
      msg_i <- nth witness msg i;
      sk_i <- nth witness (val sk) i;
      sig_i <@ Chain.chain (sk_i, 0, msg_i, _seed, address);
      sig <- put sig i sig_i;
      i <- i + 1;
    }

    return insubd sig;
  }

  proc sign_seed (M : W8.t list, sk_seed : seed, pub_seed : seed, address : adrs) : wots_signature = {
    var wots_skey : wots_sk;
    var csum_32 : W32.t;
    var csum : int;
    var msg : int list;
    var msg_i : int;
    var sk_i : nbytes;
    var len_2_bytes : int;
    var csum_bytes : W8.t list;
    var csum_base_w : int list;
    var sig : nbytes list;
    var sig_i : nbytes;
    var i : int;

    sig <- nseq len witness;

    (* Generate sk from the secret seed *)
    wots_skey <@ pseudorandom_genSK(sk_seed, pub_seed, address); 

    (* Convert message to base w *)
    msg <@ BaseW.base_w(M, len1);

    (* Compute checksum *)
    csum <@ checksum(msg);
    csum_32 <- W32.of_int csum;

    (* Convert checksum to base w *)
    csum_32 <- csum_32 `<<` W8.of_int (8 - ((ceil (len2%r * log2(w%r))) %% 8));
    len_2_bytes <- (ceil ((ceil (len2%r * log2(w%r)))%r / 8%r));

    (* msg = msg || base_w(toByte(csum, len_2_bytes), w, len_2); *)
    csum_bytes <- toByte csum_32 len_2_bytes;
    csum_base_w <@ BaseW.base_w(csum_bytes, len2);
    msg <- msg ++ csum_base_w;

    i <- 0;
    while (i < len) {
      address <- set_chain_addr address i;
      msg_i <- nth witness msg i;
      sk_i <- nth witness (val wots_skey) i;
      sig_i <@ Chain.chain (sk_i, 0, msg_i, pub_seed, address);
      sig <- put sig i sig_i;
      i <- i + 1;
    }

    return insubd sig;
  }

  proc pkFromSig(M : wots_message, sig : wots_signature, _seed : seed, address : adrs) : wots_pk = {
    var tmp_pk : nbytes list;
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

    tmp_pk <-  nseq len witness;
    (* Convert message to base w *)
    msg <@ BaseW.base_w(val M, len1);

    (* Compute checksum *)
    csum <@ checksum(msg);
    csum_32 <- W32.of_int csum;

    (* Convert checksum to base w *)
    csum_32 <- csum_32 `<<` W8.of_int (8 - (len2 * floor (log2 w%r)) %% 8);
    len_2_bytes <- (ceil ((ceil (len2%r * log2(w%r)))%r / 8%r));

    (* msg = msg || base_w(toByte(csum_32, len_2_bytes), w, len_2); *)
    csum_bytes <- toByte csum_32 len_2_bytes;
    csum_base_w <@ BaseW.base_w(csum_bytes, len2);
    msg <- msg ++ csum_base_w;
        
    i <- 0;
    while (i < len) {
      address <- set_chain_addr address i;
      msg_i <- nth witness msg i;
      sig_i <- nth witness (val sig) i;
      pk_i <@ Chain.chain (sig_i, msg_i, (w - 1 - msg_i), _seed, address);
      tmp_pk <- put tmp_pk i pk_i; 
      i <- i + 1;
    }

    return insubd tmp_pk;
  }

  proc verify(pk : wots_pk, M : wots_message, sig : wots_signature, _seed : seed, address : adrs) : bool = {
    var tmp_pk : wots_pk;
    tmp_pk <@ pkFromSig(M, sig, _seed, address);
    return pk = tmp_pk;
  }
}.

