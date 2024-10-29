require import AllCore List RealExp IntDiv.
require (*  *) Subtype. 

require import XMSS_MT_Params WOTS.

from Jasmin require import JModel.

require import Types Array8 LTree.

(******************************************************************************)

clone export Subtype as AuthPath with
  type T = nbytes list,
  op P = fun l => size l = h %/ d (* Section 4.1.8. of the RFC *)
                             (* The size is h / d for the multi tree variant *)
  rename "sT" as "auth_path"
  proof inhabited by  admit (* (exists (nseq h witness);smt(size_nseq ge0_h ge0_d)) *)
  proof *.

type sig_t = { sig_idx : W32.t;
               r : nbytes ;
               r_sigs : (wots_signature * auth_path) list }.

(******************************************************************************)

op append_sig (sig : sig_t) (r_sig : wots_signature * auth_path) : sig_t =    
    let new_sigs: (wots_signature * auth_path) list = sig.`r_sigs ++ [r_sig] in
    {| sig with  r_sigs=new_sigs|}.
