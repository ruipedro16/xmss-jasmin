require import List.
from Jasmin require import JModel.

require import Params WOTS LTree.

type xmss_sk = { idx : W32.t ;
                 sk_seed : nbytes ; (* secret *)
                 sk_prf : nbytes ;
                 pub_seed_sk : nbytes ; (* public *)
                 sk_root : nbytes }.

(* Same as single tree variant *)
type xmss_pk = { pk_oid : W32.t ;
                 pk_root : nbytes ;
                 pk_pub_seed : nbytes }.

type msg_t = W8.t list.


type xmss_keypair = xmss_sk * xmss_pk.
