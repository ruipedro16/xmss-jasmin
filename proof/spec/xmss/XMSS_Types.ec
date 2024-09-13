require import AllCore List RealExp IntDiv.
require (*  *) Subtype. 

require import XMSS_Params.

from Jasmin require import JModel.

require import Array8.

type adrs = W32.t Array8.t.

type nbytes = W8.t list. (* size = n *)
type len_n_bytes = nbytes list. (* list of length len, each element of length n *)
type len1_bytes = W8.t list. (* list of length len1 *)

(******************************************************************************)

type key = nbytes.
type seed = nbytes.

(******************************************************************************)

type wots_message = nbytes.
type wots_message_base_w = len1_bytes.
type wots_signature = len_n_bytes.
type wots_pk = len_n_bytes.
type wots_sk = len_n_bytes.
type wots_keypair = wots_pk * wots_sk.

(******************************************************************************)

clone import Subtype as OTSKeys with 
   type T = wots_sk list,
   op P = fun l => size l = 2^h
   rename "T" as "wots_ots_keys".

clone import Subtype as Three_NBytes with 
   type T = W8.t list,
   op P = fun l => size l = 3 * n
   rename "T" as "three_n_bytes"
   proof inhabited by (exists (nseq (3*n) W8.zero);smt(size_nseq ge0_n))
   proof *.

(* treeheight . n *)
clone import Subtype as AuthPath with
  type T = nbytes list,
  op P = fun l => size l = d
  rename "T" as "auth_path"
  proof inhabited by admit
  proof *.

(******************************************************************************)

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

type reduced_signature = wots_signature * auth_path.

type sig_t = { sig_idx : W32.t;
               r : nbytes ;
               r_sigs : reduced_signature list }.

type xmss_keypair = xmss_sk * xmss_pk.

(******************************************************************************)
