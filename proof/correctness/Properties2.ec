pragma Goals : printall.

require import AllCore List RealExp IntDiv.

from Jasmin require import JModel JArray.

require import Params WOTS.
require import XMSS_IMPL Parameters.

require import Array2 Array3 Array8 Array32 Array64 Array67 Array96 Array2144.

require import Correctness_Mem Correctness_Hash. 


require import BitEncoding.
(*---*) import BitChunking. 

lemma checksum_bounds : 
    len1 = XMSS_WOTS_LEN1 /\ w = XMSS_WOTS_W =>
    hoare [
      WOTS.checksum :
      size m = 64 /\
      forall (x : int), x \in m => 0 <= x < w
      ==>
      0 <= res <= len1 * (w - 1) 
    ].
proof.
rewrite /XMSS_WOTS_LEN1 /XMSS_WOTS_W => [#] len1_val w_val.
proc.
conseq (: 
  size m = 64 /\
  forall (k : int), 0 <= k < 64 => 0 <= nth witness m k < 16
  ==> _
); first by auto => /> *; smt(@List). 
while (
  size m = 64 /\
  (forall (k : int), 0 <= k < 64 => 0 <= nth witness m k < 16) /\
  0 <= i <= 64 /\
  0 <= checksum <= i * (w - 1)
); first by auto => /> /#. 
auto => /> &hr ? H0 k j.
rewrite len1_val w_val //= => H2 H3 H4 H5.
(have ->: j = 64 by smt()) => /#. 
qed.

lemma wots_checksum_ll : islossless WOTS.checksum. 
proof.
proc.
while (true) (len1 - i) ; by auto => /> /#.
qed.

lemma p_checksum_bounds : 
    len1 = XMSS_WOTS_LEN1 /\ w = XMSS_WOTS_W =>
    phoare [
      WOTS.checksum :
      size m = 64 /\
      forall (x : int), x \in m => 0 <= x < w
      ==>
      0 <= res <= len1 * (w - 1) 
    ] = 1%r.
proof.
move => [#] ??. 
conseq wots_checksum_ll (checksum_bounds _); [auto | smt() | smt()]. 
qed.
