pragma Goals : printall.

require import AllCore List RealExp IntDiv Distr DList.
require (*--*) Subtype. 

from Jasmin require import JModel.
 
require import XMSS_MT_Types XMSS_MT_Params XMSS_MT_Notation XMSS_MT_Address XMSS_MT_Hash XMSS_MT_Primitives XMSS_MT_Wots XMSS_MT_Util.

require import XMSS_MT_Commons.

import OTSKeys Three_NBytes AuthPath.
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
      address <- set_layer_addr address (d - 1);
      
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
   proc sign(sk : xmss_mt_sk, m : msg_t) : sig_t * xmss_mt_sk = {
      var sig : sig_t;
      var idx : W32.t <-sk.`idx;
      var idx_new : W32.t;
      var idx_bytes : W8.t list;
      var idx_nbytes : nbytes <- nseq n W8.zero;
      var idx_tree : W32.t;
      var idx_leaf : W32.t;
      var _R : nbytes <- nseq n W8.zero;
      var _M' : nbytes <- nseq n W8.zero;
      var address : adrs <- zero_address;
      var root : nbytes <- sk.`sk_root;
      var t : three_n_bytes <- nseq (3*n) W8.zero;
      var sk_prf : nbytes <- sk.`sk_prf;
      var j : int;
      var pub_seed : nbytes <- sk.`pub_seed_sk;
      var sig_tmp : wots_signature;
      var auth : auth_path;
    

      (* Update the key index *)
      idx_new <- idx + W32.one;
      sk <- {| sk with idx=idx_new |};

      idx_bytes <- toByte idx 32;
      _R <@ Hash.prf(sk_prf, idx_bytes);

      idx_nbytes <- toByte idx n;
      t <- _R ++ root ++ idx_nbytes; (* t = r || getRoot(SK_MT) || (toByte(idx_sig, n)) *)
      _M' <- H_msg t m;

      idx_tree <- idx `>>>` (h %/ d);
      idx_leaf <- idx `&` W32.of_int (2^(h %/ d) - 1);

      address <- set_layer_addr address 0;
      address <- set_tree_addr address (W32.to_uint idx_tree);

      (sig_tmp, auth, address) <@ TreeSig.treesig(_M', sk, idx_leaf, address);
     
      sig <- {| sig_idx = idx_leaf; r = _R; r_sigs = [(sig_tmp, auth)] |};

      j <- 1;
      while (j < d) {
      (root, address) <@ TreeHash.treehash(sk, 0, h %/ d, address);
      idx_leaf <- idx_tree `&` W32.of_int (2^(h %/ d) - 1);
      idx_tree <- idx_tree `>>>` (h %/ d);

      address <- set_layer_addr address j;
      address <- set_tree_addr address (W32.to_uint idx_tree);

      (sig_tmp, auth, address) <@ TreeSig.treesig(root, sk, idx_leaf, address);
      
      sig <- append_sig sig (sig_tmp, auth);
      
       
      j <- j+1;
    }
      

      return (sig, sk);
   }

  (* Algorithm 14 *)
   proc verify(pk : xmss_mt_pk, m : msg_t, s : sig_t) : bool = {
       var is_valid : bool;
       var idx_sig : W32.t;
       var seed : nbytes;
       var idx_bytes : nbytes;
       var node, root, _R, _M': nbytes;
       var t : three_n_bytes;
       var address : adrs;
       var idx_leaf : W32.t;
       var idx_tree : W32.t;
       var sig_ots : wots_signature;
       var auth : auth_path;
       var j : int;
     
       idx_sig <- s.`sig_idx;
       seed <- pk.`pk_pub_seed;
       idx_bytes <- toByte idx_sig n;
       address <- zero_address;
       idx_tree <- idx_sig `>>>` (h %/ d);
       idx_leaf <- idx_sig `&` W32.of_int (2^(h %/ d) - 1);
     
       (auth,sig_ots) <- nth witness s.`r_sigs 0;
     
       (* M' = H_msg(getR(Sig_MT) || getRoot(PK_MT) || (toByte(idx_sig, n)), M); *)
       root <- pk.`pk_root;
       _R <- s.`r;
       t <- _R ++ root ++ idx_bytes;
       _M' <- H_msg t m; 

       address <- set_layer_addr address 0;
       address <- set_tree_addr address (W32.to_uint idx_tree);

       node <@ RootFromSig.rootFromSig(idx_leaf, sig_ots, auth, _M', seed, address);
     
       j <- 1;
       while (j < d) {
         idx_leaf <- idx_tree `&` W32.of_int (2^(h %/ d) - 1);
         idx_tree <- idx_tree `>>>` (h %/ d);

         (auth,sig_ots) <- nth witness s.`r_sigs j;

         address <- set_layer_addr address j;
         address <- set_tree_addr address (W32.to_uint idx_tree);
       
         node <@ RootFromSig.rootFromSig(idx_leaf, sig_ots, auth, _M', node, address);

         j <- j + 1;
       }

      is_valid <- (node = root);
      return is_valid;
   }
}.

lemma sample_randomness_ll : islossless XMSS_MT_PRF.sample_randomness by proc; islossless.

lemma sample_randomness_size :
    hoare [XMSS_MT_PRF.sample_randomness : true ==> 
      size res.`1 = n /\ size res.`2 = n /\ size res.`3 = n ].
proof.
proc.
auto => />.
do 3! (move => ?; rewrite supp_dlist; [ apply ge0_n |] => [#] ??).
do split => //=.
qed.

lemma p_sample_randomness_size :
    phoare [XMSS_MT_PRF.sample_randomness : true ==> 
      size res.`1 = n /\ size res.`2 = n /\ size res.`3 = n ] = 1%r
        by conseq sample_randomness_ll sample_randomness_size => //=.


lemma xmss_mt_kg_ll : islossless XMSS_MT_PRF.kg.
proof.
proc.
auto => /> ; call treehash_ll; wp.
call sample_randomness_ll.
by auto.
qed.

lemma xmss_mt_sign_ll : islossless XMSS_MT_PRF.sign.
proof.
proc.
while (0 <= j <= d) (d - j) ; auto => />.
  - call treesig_ll ; auto => />. call treehash_ll. skip => /> /#.
  - progress => /#. 
  - call treesig_ll; wp.  call prf_ll; wp.  skip => />; smt(ge0_d). 
qed. 

