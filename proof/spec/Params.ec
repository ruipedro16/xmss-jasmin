pragma Goals : printall.

require import AllCore List RealExp IntDiv.

(* Height of the overall Merkle tree *)
(* XMSS_TREE_HEIGHT in the implementation *)
const h : { int | 0 < h } as h_g0.

(* Number of layers in a hypertree in XMSS^MT *)
(* d = 1 for the single-tree variant *)
(* XMSS_D in the implementation *)
(* h is a multiple of d *)
const d : { int | 0 < h /\ h %% d = 0 } as d_g0.

(* XMSS_FULL_HEIGHT in the implementation *)
op full_height (h d : int) : int = h * d.

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
