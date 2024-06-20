pragma Goals : printall.

require import AllCore List RealExp IntDiv.
from Jasmin require import JModel.
require import Params Notation Parameters Address Primitives Wots.

require import XMSS_IMPL XMSS_IMPL_PP Generic.

require import Array2 Array3 Array8 Array32 Array67 Array2144.

lemma nosmt shr_ge0 (input : W8.t Array32.t) (i : W64.t) :
    0 <= to_uint i < 32 =>
    0 <= to_uint ((SHR_32 (zeroextu32 input.[to_uint i]) (truncateu8 ((of_int 4))%W64)).`6 `&` (of_int 15)%W32).
proof.
move => [i_ge0 i_lt_32].
admit.
qed.

lemma nosmt shr_lt_15 (input : W8.t Array32.t) (i : W64.t) :
    0 <= to_uint i < 32 =>
    to_uint ((SHR_32 (zeroextu32 input.[to_uint i]) (truncateu8 ((of_int 4))%W64)).`6 `&` (of_int 15)%W32) <= 15.
proof.
move => [i_ge0 i_lt_32].
admit.
qed.


lemma nosmt base_w_67_post :
    hoare [M(Syscall).__base_w_67_32 : true ==>
      forall (k : int), 0 <= k < 67 => (0 <= to_uint res.[k] <= 15)]. (* 15 = w - 1 *)
proof.
proc.
while (
  0 <= to_uint i <= 67 /\
  0 <= to_uint total <= 15 /\
  (forall (k : int), 0 <= k < to_uint i => ( 0 <= to_uint output.[k] <= 15))
).
- if.
    + auto => /> ; progress.
        * rewrite to_uintD_small /#.
        * smt(@W64).
        * apply shr_ge0.
        * split ; [ smt(@W64) | move => ? ; admit ].
        * apply shr_lt_15.
        * split ; first by smt(@W64). move => ? ; admit.
        * pose t :=  (SHR_32 (zeroextu32 input{hr}.[to_uint in_0{hr}]) (truncateu8 ((of_int 4))%W64)).`6 `&` (of_int 15)%W32. rewrite get_setE. split ; [ smt() | move => ? ; smt ].
          case (k = to_uint i{hr}). move => ?. apply shr_ge0. split ; admit. (* add invariant sobre in *)
          move => ?. admit.
        * rewrite get_setE. 
          split ; [ smt() | move => ? ; admit ]. case (k = to_uint i{hr}). move => ?. apply shr_lt_15. split; by admit. admit.
    + auto => />. progress.
        * rewrite to_uintD_small /#. 
        * smt(@W64).
        * admit. (* add invariant sobre bits *)
        * admit.   
        * admit.
        * admit.
- auto => /> ; progress.
    + smt.
    + smt.
    + smt.
    + smt.
qed.

lemma base_w_spec_post :
    w = XMSS_WOTS_W =>
    hoare [BaseW.base_w : true ==> 
    forall (k : int), 0 <= k <= size(res) => 0 <= nth witness res k <= w - 1].
proof.
rewrite /XMSS_WOTS_W.
move => w_val.
proc.
while (
true
) ; by admit.
qed.
