require import AllCore List RealExp IntDiv.
require (*  *) Subtype. 

require import XMSS_MT_Params WOTS.

from Jasmin require import JModel.

require import Types Array8 LTree.

(******************************************************************************)

type sig_t = { sig_idx : W32.t;
               r : nbytes ;
               r_sigs : (wots_signature * auth_path) list }.

(******************************************************************************)

op append_sig (sig : sig_t) (r_sig : wots_signature * auth_path) : sig_t =    
    let new_sigs: (wots_signature * auth_path) list = sig.`r_sigs ++ [r_sig] in
    {| sig with  r_sigs=new_sigs|}.
