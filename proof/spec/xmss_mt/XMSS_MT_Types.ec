require import AllCore List RealExp IntDiv.
require (*  *) Subtype. 

require import XMSS_MT_Params WOTS.

from Jasmin require import JModel.

require import Array8.


(* treeheight . n *)
clone export Subtype as AuthPath with
  type T = nbytes list,
  op P = fun l => size l = d
  rename "T" as "auth_path"
  proof inhabited by (exists (mkseq (fun i => witness) d);rewrite /P size_mkseq;smt(ge0_d))
  proof *.

(******************************************************************************)

(* Same as single tree variant *)
type xmss_mt_sk = { idx : W32.t ;
                    sk_seed : nbytes ; (* secret *)
                    sk_prf : nbytes ;
                    pub_seed_sk : nbytes ; (* public *)
                    sk_root : nbytes }.

(* Same as single tree variant *)
type xmss_mt_pk = { pk_oid : W32.t ;
                    pk_root : nbytes ;
                    pk_pub_seed : nbytes }.

type msg_t = W8.t list.

type reduced_signature = wots_signature * auth_path.

type sig_t = { sig_idx : W32.t;
               r : nbytes ;
               r_sigs : reduced_signature list }.

type xmss_mt_keypair = xmss_mt_sk * xmss_mt_pk.

(******************************************************************************)
