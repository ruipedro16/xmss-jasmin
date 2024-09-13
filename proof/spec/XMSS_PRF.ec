pragma Goals : printall.

require import AllCore List RealExp IntDiv Distr DList.
require (*--*) Subtype. 

from Jasmin require import JModel.
 
require import Types Params Notation Parameters Address Hash Primitives Wots Util.

require import XMSS_Commons.

import OTSKeys Three_NBytes AuthPath.
import Array8.

module XMSS_PRF = {
    proc sample_randomness () : nbytes * nbytes * nbytes = {
    var sk_seed, sk_prf, pub_seed : nbytes;

    sk_seed <$ DList.dlist W8.dword n;
    sk_prf <$ DList.dlist W8.dword n;
    pub_seed <$ DList.dlist W8.dword n;

    return (sk_seed, sk_prf, pub_seed);
  }

   proc kg() : xmss_mt_keypair = {
      var pk : xmss_mt_pk <- witness;
      var sk : xmss_mt_sk <- witness;

      var sk_seed, sk_prf, pub_seed, root : nbytes <- nseq n W8.zero;

      var address : adrs <- zero_address;
      address <- set_layer_addr address 0;
      
      (sk_seed, sk_prf, pub_seed) <@ sample_randomness();

      sk <- {| idx=W32.zero;
               sk_seed=sk_seed;
               sk_prf=sk_prf;
               pub_seed_sk=pub_seed;
               sk_root=witness;
             |};

      (root, address) <@ TreeHash.treehash(sk, 0, h, address);

      sk <- {| idx=W32.zero;
               sk_seed=sk_seed;
               sk_prf=sk_prf;
               pub_seed_sk=pub_seed;
               sk_root=root;
             |};

      pk <- {| pk_oid=impl_oid; pk_root=root; pk_pub_seed=pub_seed |};

      return (sk, pk);
   }

proc sign(sk : xmss_mt_sk, m : msg_t) : sig_t * xmss_mt_sk = {
    var idx : W32.t;
    var idx_new : W32.t;
    var address : adrs;
    var _R : nbytes;
    var _M' : nbytes;
    var ots_sig : wots_signature;
    var auth : auth_path;
    var sig : sig_t;
    var idx_bytes : W8.t list;
    var idx_nbytes : nbytes;
    var root : nbytes;
    var t : three_n_bytes;
    var sk_prf : nbytes <- sk.`sk_prf;
    
    idx <- sk.`idx;
    idx_new <- sk.`idx + W32.one;
    sk <- {| sk with idx=idx_new |};
    address <- zero_address;
    
    idx_bytes <- toByte idx 32;

    _R <@ Hash.prf(sk_prf, idx_bytes);

    idx_nbytes <- toByte idx n;
    root <- sk.`sk_root;
    t <- _R ++ root ++ idx_nbytes;
    _M' <- H_msg t m;

    (ots_sig, auth, address) <@ TreeSig.treesig(_M', sk, idx, address);

    sig <- {| sig_idx = idx; r = _R ; r_sigs = [(ots_sig, auth)] |}; 
  
    return (sig, sk);
  }

 proc verify(pk : xmss_mt_pk, m : msg_t, s : sig_t) : bool = {
    var is_valid : bool;
    var idx_sig : W32.t;
    var idx_bytes : nbytes;
    var node, root, _R, _M': nbytes;    
    var auth : auth_path;
    var sig_ots : wots_signature;
    var _seed : seed;
    var address : adrs;
    var t : three_n_bytes;

    idx_sig <- s.`sig_idx;
    idx_bytes <- toByte idx_sig n;
    _seed <- pk.`pk_pub_seed;
    address <- zero_address;
    (auth,sig_ots) <- nth witness s.`r_sigs 0;

    root <- pk.`pk_root;
    _R <- s.`r;
    t <- _R ++ root ++ idx_bytes;
    _M' <- H_msg t m;
    
    node <@ RootFromSig.rootFromSig(idx_sig, sig_ots, auth, _M', _seed, address);

    is_valid <- (node = root);

    return is_valid;
  }  
}.
