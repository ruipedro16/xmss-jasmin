require import AllCore List RealExp IntDiv.
require (*  *) Subtype. 

require export XMSS_Params WOTS.

from Jasmin require import JModel.

require import Types Array8 LTree.
import Params.

clone export Subtype as AuthPath with
  type T = nbytes list,
  op P = fun l => size l = h (* Section 4.1.8. of the RFC *)
                             (* The size is h / d for the multi tree variant *)
  rename "sT" as "auth_path"
  proof inhabited by (exists (nseq h witness);smt(size_nseq ge0_h))
  proof *.

type sig_t = { sig_idx : W32.t;
               r : nbytes ;
               r_sig : (wots_signature * auth_path) }.

(******************************************************************************)
