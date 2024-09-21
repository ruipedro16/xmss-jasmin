require import AllCore List RealExp IntDiv.
require (*  *) Subtype. 

require import XMSS_MT_Params WOTS.

from Jasmin require import JModel.

require import Array8.

(******************************************************************************)

clone import Subtype as AuthPath with
  type T = nbytes list,
  op P = fun l => size l = d
  rename "sT" as "auth_path".

type reduced_signature = wots_signature * auth_path.

type sig_t = { sig_idx : W32.t;
               r : nbytes ;
               r_sigs : reduced_signature list }.

(******************************************************************************)