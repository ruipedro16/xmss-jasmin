require import AllCore List RealExp IntDiv.
require (*  *) Subtype. 

require export XMSS_Params WOTS.

from Jasmin require import JModel.

require import Types Array8.
import Params.

clone import Subtype as AuthPath with
  type T = nbytes list,
  op P = fun l => size l = d 
  rename "sT" as "auth_path".

type sig_t = { sig_idx : W32.t;
               r : nbytes ;
               r_sig : reduced_signature }.

(******************************************************************************)
