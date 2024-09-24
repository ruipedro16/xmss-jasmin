require import AllCore List RealExp IntDiv.
require (*  *) Subtype. 

require export XMSS_Params WOTS.

from Jasmin require import JModel.

require import Types Array8 LTree.
import Params.

type sig_t = { sig_idx : W32.t;
               r : nbytes ;
               r_sig : (wots_signature * auth_path) }.


(******************************************************************************)
