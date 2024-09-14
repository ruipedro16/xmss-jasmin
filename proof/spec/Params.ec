require import AllCore List RealExp IntDiv.
require Subtype.

from Jasmin require import JModel.

(* Height of the overall Merkle tree *)
(* XMSS_TREE_HEIGHT in the implementation *)
const h : { int | 0 < h } as h_g0.

(*  A tree of height h has 2^h leaf nodes *)
op nr_leaves (h : int) : int = 2^h.

(* Length the digest *)
const n : { int | 0 <= n } as ge0_n.

(* Winternitz parameter: the range of indices into a wots chain *)
op w : { int | w = 4 \/ w = 16} as w_vals.

const len1 : int = ceil (8%r * n%r / log2 w%r).
const len2 : int = floor (log2 (len1 * (w - 1))%r / log2 w%r) + 1.
const len : int = len1 + len2.

axiom ge0_h : 0 <= h.
axiom ge0_len  : 0 <= len.
axiom ge0_len1 : 0 <= len1.


clone export Subtype as NBytes with 
   type T = W8.t list,
   op P = fun l => size l = n
   rename "T" as "nbytes".

clone export Subtype as LenNBytes with 
   type T = nbytes list,
   op P = fun l => size l = len
   rename "T" as "len_nbytes".

clone export Subtype as OneByte with 
   type T = W8.t list,
   op P = fun l => size l = 1
   rename "T" as "onebyte".

clone export Subtype as TheeNBytes with 
   type T = W8.t list,
   op P = fun l => size l = 3 * n
   rename "T" as "threen_bytes"
   proof inhabited by (exists (nseq (3*n) W8.zero);smt(size_nseq ge0_n))
   proof *.

