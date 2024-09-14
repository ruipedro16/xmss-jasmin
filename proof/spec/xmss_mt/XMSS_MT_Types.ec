require import AllCore List RealExp IntDiv.
require (*  *) Subtype. 

require import XMSS_MT_Params Types WOTS.

from Jasmin require import JModel.

require import Array8.

(******************************************************************************)

type sig_t = { sig_idx : W32.t;
               r : nbytes ;
               r_sigs : reduced_signature list }.

(******************************************************************************)
