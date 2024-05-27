pragma Goals : printall.


require import AllCore List RealExp IntDiv.
from Jasmin require import JModel.
require import Notation Parameters Address Primitives Wots.
require import XMSS_IMPL XMSS_IMPL_PP Parameters.
require import Generic Properties.
require import Array2 Array3 Array8 Array32 Array67 Array2144.

lemma array3_list_put ['a] (x : 'a Array3.t) (v : 'a) (i : int) : put (to_list x) i v = to_list (x.[i <- v]) by admit.

lemma array67_list_put ['a] (x : 'a Array67.t) (v : 'a) (i : int) : put (to_list x) i v = to_list (x.[i <- v]) by admit.

lemma zero (x : int) :
    0 <= x <= W64.max_uint =>
       W64.of_int x = W64.zero <=> x = 0.
proof. move => ? ; split => // ; by smt(@W64). qed.

(******************************************* BASE W ******************************************************)

lemma base_w_generic_1 (_output : W32.t Array3.t, _input : W8.t Array2.t) :
    equiv[M(Syscall).__base_w_3_2 ~ BaseWGeneric.__base_w :
       arg{1} = (_output, _input) /\ arg{2} = (to_list _output, W64.of_int 3, to_list _input) ==>
    res{2} = to_list res{1}].
proof.
proc.
while (
  outlen{2} = W64.of_int 3 /\ 
  ={in_0, bits, out, consumed, total} /\
  0 <= to_uint consumed{1} <= 3 /\
  0 <= to_uint out{1} <= 3 /\
  out{1} = consumed{1} /\ 0 <= to_uint in_0{2} <= to_uint consumed{2} /\ 
  input{2} = (to_list input{1}) /\ output{2} = to_list output{1} 
); 
last by auto => />.
if; 1: by auto.
auto => />.
move => &1 &2 *.
do split.
smt(@W64).
smt(@W64).
smt(@W64).
smt(@W64).
smt(@W64).
smt(@W64).
apply (eq_from_nth witness).
smt(size_put Array3.size_to_list).
move => i ib *. 
rewrite (nth_put witness).
smt(Array3.size_to_list @W64).
pose xx :=  (
     output{1}.[to_uint consumed{2} <-
       (SHR_32 (zeroextu32 input{1}.[to_uint in_0{2}])
          (truncateu8 ((of_int 4))%W64)).`6 `&`
       (of_int 15)%W32]).
rewrite (Array3.get_to_list xx i) /xx.
case (to_uint consumed{2}=i).
move => h. rewrite get_setE. smt(@W64). rewrite ifT. smt(). 
do congr.
move => h ; smt(@List @Array3 @Array2).
auto => />.
move => *.
do split.
smt(@W64).
smt(@W64).
smt(@W64).
smt(@W64).
smt(@W64).
smt(array3_list_put).
qed.

lemma base_w_generic_2 (_output : W32.t Array67.t, _input : W8.t Array32.t) :
    equiv[M(Syscall).__base_w_67_32 ~ BaseWGeneric.__base_w :
       arg{1} = (_output, _input) /\ arg{2} = (to_list _output, W64.of_int 67, to_list _input) ==>
    res{2} = to_list res{1}].
proof.
proc.
while (
  outlen{2} = W64.of_int 67 /\ 
  ={in_0, bits, out, consumed, total} /\
  0 <= to_uint consumed{1} <= 67 /\
  0 <= to_uint out{1} <= 67 /\
  out{1} = consumed{1} /\ 0 <= to_uint in_0{2} <= to_uint consumed{2} /\ 
  input{2} = (to_list input{1}) /\ output{2} = to_list output{1} 
); 
last by auto => />.
if; 1: by auto.
auto => />.
move => &1 &2 *.
do split.
smt(@W64).
smt(@W64).
smt(@W64).
smt(@W64).
smt(@W64).
smt. (* smt(@W64) fails *)
apply (eq_from_nth witness).
smt(size_put Array67.size_to_list).
move => i ib *. 
rewrite (nth_put witness).
smt(Array67.size_to_list @W64).
pose xx :=  (
     output{1}.[to_uint consumed{2} <-
       (SHR_32 (zeroextu32 input{1}.[to_uint in_0{2}])
          (truncateu8 ((of_int 4))%W64)).`6 `&`
       (of_int 15)%W32]).
rewrite (Array67.get_to_list xx i) /xx.
case (to_uint consumed{2}=i).
move => h. rewrite get_setE. smt(@W64). rewrite ifT. smt(). 
do congr.
move => h ; smt(@List @Array32 @Array67).
auto => />.
move => *.
do split.
smt(@W64).
smt(@W64).
smt(@W64).
smt(@W64).
smt. (* smt(@W64) fails *)
smt(array67_list_put).
qed.

(* We need to prove that (nth witness X{`&2} _in{`&2} `>>`  (of_int (bits{`&2} + 8 - floor (log2 w%r)))%W8) `&`  (of_int (w - 1))%W8))
((SHR_32 (zeroextu32 (nth witness X{`&2} (to_uint ((of_int _in{`&2}))%W64))) (truncateu8 ((of_int (bits{`&2} + 4)))%W64)).`6 `&` (of_int 15)%W32)) *)

lemma base_w_correctness (x_out : W32.t list, len_out : int, in_list : byte list) :
    (len_out = XMSS_WOTS_LEN \/ len_out = XMSS_WOTS_LEN2) /\ (* len_out is either len2 or len *)
    w = XMSS_WOTS_W /\
    floor (log2 w%r) = XMSS_WOTS_LOG_W => (* log2 w is a precomputed parameter *)
      equiv[BaseWGeneric.__base_w ~ BaseW.base_w :
        arg{1} = (x_out, W64.of_int len_out, in_list) /\
        arg{2} = (in_list, len_out) ==> 
          res{1} = map W32.of_int res{2}].
proof.
rewrite /XMSS_WOTS_W /XMSS_WOTS_LOG_W.
move => H.
move: H => [#] len__out w_vals logw.
proc ; inline.
auto => /> *.
while (
  outlen{2} = len_out /\
  outlen{1} = W64.of_int outlen{2} /\
  consumed{1} = W64.of_int consumed{2} /\
  input{1} = X{2} /\
  bits{2} = to_uint bits{1} /\
  ={total} /\
  _in{2} = to_uint in_0{1} /\ 
  to_uint in_0{1} + 1 < W64.max_uint /\
  0 <= consumed{2} <= outlen{2} /\
  0 <= _in{2} < outlen{2}  /\
  forall (k : int), (0 <= k < consumed{2}) => to_uint (nth witness output{1} k) = nth witness base_w{2} k
).
(* ------------------------- first subgoal of while starts here ------------------------- *)
if.
(* 1st goal of if *)
auto => /> &1 &2 *.
smt(@W64).
(* 2nd goal of if *)
auto => /> &1 &2 *.
do split.
rewrite logw //=. (* 1st subgoal of split *)
smt.
admit. (* 2nd subgoal of split *)
smt(). (* 3rd subgoal of split *)
smt(). (* 4th subgoal of split *)
smt(). (* 5th subgoal of split *)
simplify.
smt(). (* 6th subgoal of split *)
smt. (* 9th *)
(* 3rd subgoal of if *)
auto => /> *.
do split ; 2,3,4,6: by smt().
(* 1 *) rewrite logw //=.
(* 5 *) admit. (*`move => *. rewrite logw w_val /=. split. admit. admit. smt. *)
(* 7 *) smt.
(* ------------------------- second subgoal of while starts here ------------------------- *)
auto => /> *.
do split; 1,2: by smt().
(* 3 *) smt.
(* 4 *) smt.
qed.


lemma base_w_ll : islossless BaseWGeneric.__base_w.
proof.
proc.
islossless.
while (true) ((to_uint outlen) - (to_uint consumed)) ; last by auto => /> /#.
auto => /> *.
smt.
qed.

(*********************************** EXPAND SEED ************************************************)

lemma expand_seed_ll : islossless Mp(Syscall).__expand_seed_.
proof.
proc ; inline => //=.
islossless.
while (true) (67 - i) => //= ; last by skip => /#. 
auto => /> *.
islossless ; first by smt().
while (true) (8 - i1) ; last by skip ; auto => /> /#.
auto => /> /#.
while (true) (inlen - (to_uint i0)) => //=.
auto => /> *.
smt.
skip ; auto => /> *. 
smt.
qed.

(****************************** GEN CHAIN ********************************************************)

lemma wots_gen_chain_ll: islossless Mp(Syscall).__gen_chain_inplace.
proof.
proc ; inline => /=.
islossless => //=.
admit.
qed.


(***************************************************************************************)

(* Pseudorandom key generation *)
(* During key generation, a uniformly random n-byte string S is
sampled from a secure source of randomness. This string S is stored
as private key. The private key elements are computed as sk[i] =
PRF(S, toByte(i, 32)) whenever needed.
*)


lemma correctness_wots_gen_pk(pk : W8.t Array2144.t, 
                              seed:W8.t Array32.t,
                              pub_seed:W8.t Array32.t, 
                              addr:W32.t Array8.t) :
    equiv[WOTS.genPK ~ Mp(Syscall).__wots_pkgen : 
        arg{2} = (pk, seed, pub_seed, addr) ==> true ].
proof.
admit.
qed.

(**************************************** CHECKSUM ***********************************)

lemma wots_checksum_lossless : islossless Mp(Syscall).__wots_checksum.
proof.
proc.
islossless.
(* 1st subgoal *)
while (true) ((to_uint outlen) - (to_uint consumed)); last by skip ; smt.
auto => /> *. 
smt.
(* 2nd subgoal *)
while (true) (i - aux); last by skip ; smt.
auto => /> *.
smt.
(* 3rd subgoal *)
while (true) (64 - (to_uint i)); last by skip ; smt.
auto => /> *.
smt.
qed.

lemma wots_checksum_ll : islossless Mp(Syscall).__csum.
proof. proc. while (true) (64 - (to_uint i)); by auto => /> * ; smt. qed.

lemma wots_checksum_correctness (msg : W32.t Array67.t) :
    len1 = XMSS_WOTS_LEN1 => 
    w = XMSS_WOTS_W =>
    equiv [Mp(Syscall).__csum ~ Checksum.checksum :
      arg{1} = msg /\ arg{2} = to_list msg ==> to_uint res{1} = to_uint res{2}].
proof.
rewrite /XMSS_WOTS_LEN_1 /XMSS_WOTS_W ; move => ? ?.
proc => /=.
while (
  i{2} = to_uint i{1} /\
  m{2} = to_list msg_base_w{1} /\
  0 <= i{2} <= len1
).
auto => /> *.
do split; 1,2,3,4,5: by smt.
auto => /> *.
split; 1: by smt().
auto => /> *. smt.
qed.

(* FIX THIS LEMMA *)
lemma wots_checksum(csum_base_w : W32.t Array3.t, msg_base_w : W32.t Array67.t) :
    len1 = XMSS_WOTS_LEN1 =>
    len2 = XMSS_WOTS_LEN2 =>
    len = XMSS_WOTS_LEN =>
    w = XMSS_WOTS_W =>
    hoare[Mp(Syscall).__wots_checksum :
      arg = (csum_base_w, msg_base_w) ==> true].
proof.
move => ? ? ? ?.
proc.
auto => /> *.
qed.

(*********************************************************************************)
