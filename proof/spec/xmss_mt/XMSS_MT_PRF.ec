pragma Goals : printall.

require import AllCore List RealExp IntDiv Distr DList.
require (*--*) Subtype. 

from Jasmin require import JModel.
 
require import Types XMSS_MT_Types Address BaseW Hash WOTS LTree XMSS_MT_TreeHash.

import XMSS_MT_Params Params OTSKeys TheeNBytes AuthPath.
import Array8.

module XMSS_MT_PRF = {
   (* Different from the spec because we use a secret seed instead of the full wots keys *)
   (* Algorithm 10 instead of 15 *)
   (*
            +---------------------------------+
            |          algorithm OID          |     W32 (4 bytes)
            +---------------------------------+
            |                                 |
            |            root node            |     n bytes
            |                                 |
            +---------------------------------+
            |                                 |
            |              SEED               |     n bytes
            |                                 |
            +---------------------------------+

                            XMSS^MT Public Key
   *)

  proc sample_randomness () : nbytes * nbytes * nbytes = {
    var sk_seed, sk_prf, pub_seed : W8.t list;

    sk_seed  <$ DList.dlist W8.dword n;
    sk_prf   <$ DList.dlist W8.dword n;
    pub_seed <$ DList.dlist W8.dword n;

    return (NBytes.insubd sk_seed, NBytes.insubd sk_prf, NBytes.insubd pub_seed);
  }

   proc kg() : xmss_keypair = {
      var pk : xmss_pk <- witness;
      var sk : xmss_sk <- witness;

      var sk_seed, sk_prf, pub_seed, root : nbytes;

      var address : adrs <- zero_address;
      address <- set_layer_addr address (d - 1);
      
      (sk_seed, sk_prf, pub_seed) <@ sample_randomness();

      sk <- {| idx=W32.zero;
               sk_seed=sk_seed;
               sk_prf=sk_prf;
               pub_seed_sk=pub_seed;
               sk_root=witness;
             |};

      root <@ TreeHash.treehash(pub_seed, sk_seed, 0, h %/ d, address);

      sk <- {| idx=W32.zero;
               sk_seed=sk_seed;
               sk_prf=sk_prf;
               pub_seed_sk=pub_seed;
               sk_root=root;
             |};

      pk <- {| pk_oid=impl_oid; pk_root=root; pk_pub_seed=pub_seed |};

      return (sk, pk);
   }

   (*
           +---------------------------------+
           |                                 |
           |          index idx_sig          |   ceil(h / 8) bytes
           |                                 |
           +---------------------------------+
           |                                 |
           |          randomness r           |   n bytes
           |                                 |
           +---------------------------------+
           |                                 |
           |  (reduced) XMSS signature Sig   |   (h / d + len) * n bytes
           |        (bottom layer 0)         |
           |                                 |
           +---------------------------------+
           |                                 |
           |  (reduced) XMSS signature Sig   |   (h / d + len) * n bytes
           |            (layer 1)            |
           |                                 |
           +---------------------------------+
           |                                 |
           ~              ....               ~
           |                                 |
           +---------------------------------+
           |                                 |
           |  (reduced) XMSS signature Sig   |   (h / d + len) * n bytes
           |          (layer d - 1)          |
           |                                 |
           +---------------------------------+

                             XMSS^MT Signature
   *)
   proc sign(sk : xmss_sk, m : msg_t) : sig_t * xmss_sk = {
      var sig : sig_t;
      var idx : W32.t <-sk.`idx;
      var idx_new : W32.t;
      var idx_bytes : nbytes;
      var idx_tree : W32.t;
      var idx_leaf : W32.t;
      var _R : nbytes;
      var _M' : nbytes;
      var address : adrs;
      var root : nbytes;
      var t : threen_bytes;
      var sk_prf : nbytes;
      var j : int;
      var pub_seed : nbytes;
      var sig_tmp : wots_signature;
      var auth : auth_path;
    
      address  <- zero_address;
      root  <- sk.`sk_root;
      sk_prf <- sk.`sk_prf;

      (* Update the key index *)
      idx_new <- idx + W32.one;
      sk <- {| sk with idx=idx_new |};

      idx_bytes <- NBytes.insubd (toByte idx n);
      _R <@ Hash.prf(idx_bytes, sk_prf);

      t <- TheeNBytes.insubd (val _R ++ val root ++ val idx_bytes); (* t = r || getRoot(SK_MT) || (toByte(idx_sig, n)) *)
      _M' <- H_msg t m;

      idx_tree <- idx `>>>` (h %/ d);
      idx_leaf <- idx `&` W32.of_int (2^(h %/ d) - 1);

      address <- set_layer_addr address 0;
      address <- set_tree_addr address (W32.to_uint idx_tree);

      (sig_tmp, auth) <@ TreeSig.treesig(_M', sk, idx_leaf, address);
     
      sig <- {| sig_idx = idx_leaf; r = _R; r_sigs = [ (sig_tmp, auth) ] |};

      j <- 1;
      while (j < d) {
      root <@ TreeHash.treehash(sk.`pub_seed_sk, sk.`sk_seed, 0, h %/ d, address);
      idx_leaf <- idx_tree `&` W32.of_int (2^(h %/ d) - 1);
      idx_tree <- idx_tree `>>>` (h %/ d);

      address <- set_layer_addr address j;
      address <- set_tree_addr address (W32.to_uint idx_tree);

      (sig_tmp, auth) <@ TreeSig.treesig(root, sk, idx_leaf, address);
      
      sig <- append_sig sig (sig_tmp, auth); 
      
       
      j <- j+1;
    }
      

      return (sig, sk);
   }

  (* Algorithm 14 *)
   proc verify(pk : xmss_pk, m : msg_t, s : sig_t) : bool = {
       var is_valid : bool;
       var idx_sig : W32.t;
       var seed : nbytes;
       var idx_bytes : nbytes;
       var node, root, _R, _M': nbytes;
       var t : threen_bytes;
       var address : adrs;
       var idx_leaf : W32.t;
       var idx_tree : W32.t;
       var sig_ots : wots_signature;
       var auth : auth_path;
       var j : int;
     
       idx_sig <- s.`sig_idx;
       idx_bytes <- NBytes.insubd (toByte idx_sig n);
       seed <- pk.`pk_pub_seed;
       address <- zero_address;
       idx_tree <- idx_sig `>>>` (h %/ d);
       idx_leaf <- idx_sig `&` W32.of_int (2^(h %/ d) - 1);
     
       (sig_ots,auth) <- nth witness s.`r_sigs 0; 
     
       (* M' = H_msg(getR(Sig_MT) || getRoot(PK_MT) || (toByte(idx_sig, n)), M); *)
       root <- pk.`pk_root;
       _R <- s.`r;
       t <- TheeNBytes.insubd (val _R ++ val root ++ val idx_bytes);
       _M' <- H_msg t m; 

       address <- set_layer_addr address 0;
       address <- set_tree_addr address (W32.to_uint idx_tree);

       node <@ RootFromSig.rootFromSig(idx_leaf, sig_ots, auth, _M', seed, address);
     
       j <- 1;
       while (j < d) {
         idx_leaf <- idx_tree `&` W32.of_int (2^(h %/ d) - 1);
         idx_tree <- idx_tree `>>>` (h %/ d);

         (sig_ots,auth) <- nth witness s.`r_sigs j; 

         address <- set_layer_addr address j;
         address <- set_tree_addr address (W32.to_uint idx_tree);
       
         node <@ RootFromSig.rootFromSig(idx_leaf, sig_ots, auth, _M', node, address);

         j <- j + 1;
       }

      is_valid <- (node = root);
      return is_valid;
   }
}.

