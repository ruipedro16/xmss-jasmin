require import AllCore List RealExp IntDiv.
require (*  *) Subtype. 

require export XMSS_Params WOTS.

from Jasmin require import JModel.

require import Array8.
import Params.

clone import Subtype as AuthPath with
  type T = nbytes list,
  op P = fun l => size l = d 
  rename "sT" as "auth_path".

type sig_t = { sig_idx : W32.t;
               r : nbytes ;
               r_sig : (wots_signature * auth_path) }.

type xmss_sk = { idx : W32.t ;
                 sk_seed : nbytes ; (* secret *)
                 sk_prf : nbytes ;
                 pub_seed_sk : nbytes ; (* public *)
                 sk_root : nbytes }.

type xmss_pk = { pk_oid : W32.t ;
                 pk_root : nbytes ;
                 pk_pub_seed : nbytes }.

type msg_t = W8.t list.

type xmss_keypair = xmss_sk * xmss_pk.


(******************************************************************************)
