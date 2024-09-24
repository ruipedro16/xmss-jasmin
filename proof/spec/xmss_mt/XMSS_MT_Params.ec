require import AllCore List RealExp IntDiv.

from Jasmin require import JModel.

require export Params.

(* Number of layers in a hypertree in XMSS^MT *)
(* d = 1 for the single-tree variant *)
(* XMSS_D in the implementation *)
(* h is a multiple of d *)
(* d layers of trees, each having height h/d  *)
(* hyper-tree of total height h, where h is a multiple of d *)
const d : { int | 0 < d /\ h %% d = 0 } as d_g0.
axiom ge0_d : 0 < d.

op impl_oid : W32.t.
