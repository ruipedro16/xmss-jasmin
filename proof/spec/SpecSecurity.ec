require import AllCore List Distr DList.
from Jasmin require import JModel.

require (****) XMSS_TW.
require import XMSS_PRF.
import Params Types XMSS_Types Hash WOTS Address LTree BaseW.

(* Get checksum from XMXX_Checksum and then plug those results
   here *)
clone import XMSS_TW as XMSS_ABSTRACT with
   type mseed <- nbytes,
   op dmseed <- (dmap ((dlist W8.dword n)) NBytes.insubd),
   type mkey <- nbytes * int,
   type FLXMSSTWL.SA.WTW.pseed <- nbytes,
   op FLXMSSTWL.SA.WTW.dpseed <- (dmap ((dlist W8.dword n)) NBytes.insubd),
   type FLXMSSTWL.SA.WTW.sseed <- nbytes,
   op FLXMSSTWL.SA.WTW.dsseed <- (dmap ((dlist W8.dword n)) NBytes.insubd),
   type FLXMSSTWL.SA.WTW.adrs <- adrs,
   type msgXMSSTW <- W8.t list,
   op FLXMSSTWL.n <- n,
   op FLXMSSTWL.h <- h,
   op mkg = (fun (ms : nbytes) (i : FLXMSSTWL.SA.index) => 
          let padding = lenbytes_be64 prf_padding_val padding_len in
          let in_0 = lenbytes_be32 (W32.of_int (FLXMSSTWL.SA.Index.val i)) 4 in   
          (Hash (padding ++ val ms ++ in_0),FLXMSSTWL.SA.Index.val i)).
print XMSS_TW.

import   FLXMSSTWL SA WTW.
import HtS Repro MCORO. 

module FakeRO : POracle = {
   var root : nbytes

   proc o(x : (nbytes * int) * W8.t list) : msgFLXMSSTW = {
      var t,idx_bytes;
      idx_bytes <- lenbytes_be32 (W32.of_int x.`1.`2) 4;   
      t <- (ThreeNBytesBytes.insubd (val x.`1.`1 ++ val root ++ idx_bytes));
      return DigestBlock.insubd (BytesToBits (val (H_msg t x.`2)));
   }
}.

op skrel(ask : skXMSSTW, sk : xmss_sk) =
   ask.`1 = sk.`sk_prf /\
   ask.`2.`1 = Index.insubd (to_uint sk.`idx) /\
   ask.`2.`2 = sk.`sk_seed /\
   ask.`2.`3 = sk.`pub_seed_sk
   (* ask.`2.`4 = ??? Why is the address in/not in the sk/pk? *)
   (* ??? = sk.`pk_root Why is the root not in/in the sk? *).

op pkrel(apk : pkXMSSTW, pk : xmss_pk) = 
   apk.`1 = DigestBlock.insubd (BytesToBits (val pk.`pk_root)) /\
   apk.`2 = pk.`pk_pub_seed
   (* apk.`3 = ??? Why is the address in the sk/pk? *)
   (* ??? = pk.`pk_oid I guess abstract proofs fon't care about oid *).

equiv kg_eq : XMSS_TW(FakeRO).keygen ~ XMSS_PRF.kg : ={arg} ==> pkrel res{1}.`1 res{2}.`2 /\ skrel res{1}.`2 res{2}.`1.
proc. inline {1} 2. inline {1} 5.
inline {2} 5. inline {1} 8. inline {2} 10.
admitted.

(* Signature type is abused with two index copies because I need this to simulate
   the actual operation of the implementation *)
op sigrel(asig : sigXMSSTW, sig : sig_t) =
   (* asig.`1 = ??? /\ why is the public seed in the signature ? *)
   asig.`1.`1 = sig.`r /\
   asig.`1.`2 = to_uint sig.`sig_idx /\
   asig.`2.`1 = FLXMSSTWL.SA.Index.insubd (to_uint sig.`sig_idx) /\
   asig.`2.`2 = DBLL.insubd 
     (map (fun (b : nbytes) => DigestBlock.insubd (BytesToBits (NBytes.val b))) (val sig.`r_sig.`1)) /\ 
   asig.`2.`3 = DBHL.insubd 
     (map (fun (b : nbytes) => DigestBlock.insubd (BytesToBits (NBytes.val b))) (val sig.`r_sig.`2)).


equiv sig_eq : XMSS_TW(FakeRO).sign ~ XMSS_PRF.sign : skrel sk{1} sk{2} /\ ={m} ==> 
   sigrel res{1}.`1 res{2}.`1 /\  skrel res{1}.`2 res{2}.`2. 
proc. inline {1} 6. inline {1} 8. inline {1} 14. inline {1} 20. inline {2} 7.
admitted.

equiv ver_eq : XMSS_TW(FakeRO).verify ~ XMSS_PRF.verify : pkrel pk{1} pk{2} /\ ={m} /\ sigrel sig{1} s{2} ==> 
   ={res}. 
proc. 
admitted.

