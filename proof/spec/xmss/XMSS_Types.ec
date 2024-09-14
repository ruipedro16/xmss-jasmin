require import AllCore List RealExp IntDiv.
require (*  *) Subtype. 

require export XMSS_Params WOTS.

from Jasmin require import JModel.

require import Array8.
import Params.

(* Same as single tree variant *)
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

(* treeheight . n *)
clone export Subtype as AuthPath with
  type T = nbytes list,
  op P = fun l => size l = 1
  rename "T" as "auth_path"
  proof inhabited by (exists [witness];auto)
  proof *.

type reduced_signature = wots_signature * auth_path.

type sig_t = { sig_idx : W32.t;
               r : nbytes ;
               r_sigs : reduced_signature list }.

type xmss_keypair = xmss_sk * xmss_pk.

(******************************************************************************)
