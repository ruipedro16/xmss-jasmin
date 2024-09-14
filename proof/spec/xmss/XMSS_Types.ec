require import AllCore List RealExp IntDiv.
require (*  *) Subtype. 

require export XMSS_Params WOTS Types.

from Jasmin require import JModel.

require import Array8.
import Params.

type sig_t = { sig_idx : W32.t;
               r : nbytes ;
               r_sig : reduced_signature }.

(******************************************************************************)
