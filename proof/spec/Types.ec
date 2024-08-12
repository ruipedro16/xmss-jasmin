require import AllCore List RealExp IntDiv.
require (*  *) Subtype. 

require import Params.

from Jasmin require import JModel.

require import Array8.

type adrs = W32.t Array8.t.

clone import Subtype as NBytes with 
   type T = W8.t list,
   op P = fun l => size l = n
   rename "T" as "nbytes"
   proof inhabited by (exists (nseq n W8.zero);smt(size_nseq ge0_n))
   proof *.

clone import Subtype as LEN_N with 
   type T = nbytes list,
   op P = fun l => size l = len
   rename "T" as "len_n_bytes"
   proof inhabited by (exists (nseq len (nseq n W8.zero));smt(size_nseq ge0_len))
   proof *.

clone import Subtype as LEN1 with 
   type T = W8.t list,
   op P = fun l => size l = len1
   rename "T" as "len1_bytes"
   proof inhabited by (exists (nseq len1 W8.zero);smt(size_nseq ge0_len1))
   proof *.

type key = nbytes.
type seed = nbytes.

type wots_message = nbytes.
type wots_message_base_w = len1_bytes.
type wots_signature = len_n_bytes.
type wots_pk = len_n_bytes.
type wots_sk = len_n_bytes.
type wots_keypair = wots_pk * wots_sk.
