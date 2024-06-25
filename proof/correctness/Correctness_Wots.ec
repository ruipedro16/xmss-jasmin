pragma Goals : printall.

require import AllCore List RealExp IntDiv.
from Jasmin require import JModel.
require import Params Notation Parameters Address Primitives Wots.

require import XMSS_IMPL XMSS_IMPL_PP Generic.

require import Array2 Array3 Array8 Array32 Array67 Array2144.

print mkseq.

op w32Array_to_intlist (x : W32.t Array67.t) = mkseq (fun (i : int) => to_uint x.[i]) 67.

lemma wots_checksum_correctness (msg : W32.t Array67.t) :
    len1 = XMSS_WOTS_LEN1 /\ w = XMSS_WOTS_W =>
    equiv [Mp(Syscall).__csum ~ WOTS.checksum :
      arg{1} = msg /\ arg{2} = w32Array_to_intlist msg /\ 
      forall (k : int), 0 <= k < 67 => 0 <= to_uint msg.[k] <= (w - 1) ==> 
        to_uint res{1} = to_uint res{2}].
proof.
rewrite /XMSS_WOTS_LEN1 /XMSS_WOTS_W ; move => [len1_val w_val].
proc => /=.
while (
  #pre /\
  i{2} = to_uint i{1} /\ 0 <= to_uint i{1} <= 64 /\
  m{2} = w32Array_to_intlist msg_base_w{1} /\
  0 <= i{2} <= len1 /\
  to_uint csum{1} = checksum{2} /\
  0 <= to_uint csum{1} <= W32.max_uint
).
- auto => />. move => &1 H0 H1 H2 H3 H4 H5 H6 H7 ; do split; 1,2,3,7: by rewrite to_uintD /#.
    + smt().
    + smt().
    + rewrite w_val !to_uintD /=. admit.
    + move => ?. rewrite to_uintD. admit.
    + rewrite len1_val ultE of_uintK to_uintD /= /#.
    + rewrite len1_val ultE to_uintD /= /#.
- auto => />. move => * ; do split; 1,2: by rewrite len1_val. auto => /> *. rewrite of_uintK /#. 
qed.

op w32Array_to_intlist_3 (x : W32.t Array3.t) = mkseq (fun (i : int) => to_uint x.[i]) 3.

lemma base_w_correct (o : W32.t Array3.t, _in : W8.t Array2.t) : 
    floor (log2 w%r) = XMSS_WOTS_LOG_W => 
    equiv[M(Syscall).__base_w_3_2 ~ BaseW.base_w : 
      arg{1}=(o, _in) /\ arg{2}=(to_list _in, 3) ==> res{2} = w32Array_to_intlist_3 res{1}].
proof.
rewrite /XMSS_WOTS_LOG_W ; move => logw_val.
proc.
wp ; sp.
while (
  X{2} = to_list input{1} /\
  outlen{2} = 3 /\
  0 <= to_uint i{1} <= 3 /\ consumed{2} = to_uint i{1} /\ out{2} = to_uint i{1} /\
  0 <= to_uint bits{1} <= 16 /\ (* bits <= 8 * inlen = 8 * 2 = 16 *)
  bits{2} = to_uint bits{1} /\
  to_uint total{1} = to_uint total{2} /\
  forall (k : int), 0 <= k < to_uint i{1} => to_uint output{1}.[k] = nth witness base_w{2} k
).
- if.
    + move => &1 &2 H0. move : H0 => [#] H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12. split ; smt(@W64). 
    + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 ; do split.
        * rewrite to_uintD /#.
        * rewrite to_uintD /#.
        * rewrite to_uintD /#. 
        * rewrite to_uintD /#.
        * by rewrite logw_val.
        * admit.
        * admit.
        * rewrite ultE of_uintK to_uintD /#.
        * rewrite ultE of_uintK to_uintD /#.
    + auto => />. move => &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 ; do split.
        * rewrite to_uintD /#.
        * rewrite to_uintD /#.
        * rewrite to_uintD /#. 
        * rewrite to_uintD /#.
        * rewrite to_uintD /#.
        * admit.
        * rewrite logw_val. admit.
        * admit. 
        * move => k k_ge0 ?. admit.
        * rewrite ultE of_uintK to_uintD /#.
        * rewrite ultE of_uintK to_uintD /#.
- skip => />. progress. smt. rewrite /w32Array_to_intlist_3. admit.


















lemma base_w_post : hoare [BaseW.base_w : 0 < outlen ==> all (fun (k : int) => 0 <= k < w) res].
proof.
proc.
while (
  #pre /\
  0 <= consumed <= outlen /\
  0 <= out <= outlen /\ out = consumed /\
  0 <= bits <= 8 * outlen
).

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
