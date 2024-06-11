pragma Goals : printall.

require import AllCore List RealExp IntDiv.
from Jasmin require import JModel.
require import Params Notation Parameters Address Primitives Wots.

require import XMSS_IMPL XMSS_IMPL_PP Generic.

require import Array2 Array3 Array8 Array32 Array67 Array2144.

(*****************************************************************************************************************)

lemma take_drop_3 (x : 'a Array3.t) (v : 'a) (i : int) :
    take i (mkseq ("_.[_]" x) 3) ++ v :: drop (i + 1) (mkseq ("_.[_]" x) 3) =
    mkseq ("_.[_]" x.[i <- v]) 3.
proof.
case (0 <= i /\ i < 3).
move => H. move : H => [#] i_ge0 i_lt3.
pose s := mkseq ("_.[_]" x) 3.
rewrite -put_in.
smt(size_mkseq).
admit.
move => H.
admit.
qed.


lemma array3_list_put ['a] (x : 'a Array3.t) (v : 'a) (i : int) : put (to_list x) i v = to_list (x.[i <- v]).
proof.
rewrite /to_list /put => />.
case (0 <= i /\ i < 3).
move => H.
move : H => [#] i_ge0 i_lt3.
rewrite ifT.
split ; first by apply i_ge0. 
smt(@List).
apply take_drop_3.
move => H.
rewrite ifF.
smt(@List).
congr.
smt(@Array3).
qed.


lemma take_drop_67 (x : 'a Array67.t) (v : 'a) (i : int) :
    take i (mkseq ("_.[_]" x) 67) ++ v :: drop (i + 1) (mkseq ("_.[_]" x) 67) =
    mkseq ("_.[_]" x.[i <- v]) 67.
proof.
case (0 <= i /\ i < 67).
move => H. 
move : H => [#] i_ge0 i_lt67.
pose s := mkseq ("_.[_]" x) 67.
rewrite -put_in.
smt(size_mkseq).
admit.
admit.
qed.


lemma array67_list_put ['a] (x : 'a Array67.t) (v : 'a) (i : int) : put (to_list x) i v = to_list (x.[i <- v]).
proof.
rewrite /to_list /put => />.
case (0 <= i /\ i < 67).
move => H. 
move : H => [#] i_ge0 i_lt67.
rewrite ifT.
split ; first by apply i_ge0.
smt(@List).
apply take_drop_67.
move => H.
rewrite ifF.
smt(@List).
congr.
smt(@Array67).
qed.

(*****************************************************************************************************************)

lemma foo (i y : W64.t) :
 ! (i \ult y) = y \ule i by smt.

lemma plus_one (x : W64.t) :
(*     to_uint x < W64.max_uint =>  *)
    to_uint x + 1 = to_uint (x + W64.one).
proof.
admit.
qed.


lemma lt (x y : W64.t) :
    x \ult y => x + W64.one \ule y by smt.


(*****************************************************************************************************************)


lemma f0 (x y : W64.t) : to_uint (x - y) <= 0 <=> ! (y \ult x) by smt.
lemma f1 (x y : int) : x - y <= 0 <=> ! (y < x) by smt().
lemma f2 (x y : W64.t) :
    to_uint (x - (y + W64.one)) < to_uint (x - y) by smt.

(*****************************************************************************************************************)


(* 
base w 
TERMINATION : DONE 
CORRECTNESS : Auxiliary lemmas with admit
*)
lemma base_w_ll : islossless BaseWGeneric.__base_w.
proof.
proc.
islossless.
while (true) ((to_uint outlen) - (to_uint consumed)) ; first by auto => /> *; smt(@W64).
skip.
auto => /> /#.
qed.


lemma shr_base_w (input : W8.t Array32.t) (output : W32.t Array67.t) (base_w : int list) (in_0 : W64.t) (k : int) (out : W64.t):
to_uint
  output.[to_uint out <-
    (SHR_32 (zeroextu32 input.[to_uint in_0])
       (truncateu8 ((of_int 4))%W64)).`6 `&`
    (of_int 15)%W32].[k] =
nth witness
  (put base_w (to_uint out)
     (to_uint
        ((input.[to_uint in_0] `>>` (of_int 4)%W8) `&`
         (of_int 15)%W8))) k.
proof.
admit.
qed.

lemma shr_base_w_2 (input : W8.t Array32.t) (output : W32.t Array67.t) (base_w : int list) (total : W8.t) (k : int) (bits out : W64.t):
to_uint
  output.[to_uint out <-
    (SHR_32 (zeroextu32 total) (truncateu8 (bits - (of_int 4)%W64))).`6 `&`
    (of_int 15)%W32].[k] =
nth witness
  (put base_w (to_uint out)
     (to_uint
        ((total `>>` (of_int (to_uint bits - 4))%W8) `&`
         (of_int 15)%W8))) k.
proof.
admit.
qed.


lemma base_w_correctness_67_32 (_out : W32.t Array67.t, _in_ : W8.t Array32.t) :
    w = XMSS_WOTS_W =>
    floor (log2 w%r) = XMSS_WOTS_LOG_W => 
    equiv[M(Syscall).__base_w_67_32 ~ BaseW.base_w :
      arg{1} = (_out, _in_) /\
      arg{2} = (to_list _in_, 67) ==>
        res{2} = map W32.to_uint (to_list res{1})].
proof.
rewrite /XMSS_WOTS_W /XMSS_WOTS_LOG_W.
move => w_val logw.
proc.
auto => /> *.
while (
  outlen{2} = 67 /\
  0 <= to_uint consumed{1} <= 67 /\
  consumed{2} = to_uint consumed{1} /\
  X{2} = to_list input{1} /\
  to_uint bits{1} = bits{2} /\
  ={total} /\
  0 <= _in{2} <= 67 /\
  out{2} = to_uint out{1} /\
  W64.zero \ule in_0{1} /\ in_0{1} \ule W64.of_int 67 /\
  _in{2} = to_uint in_0{1} /\
  forall (k : int), (0 <= k < out{2}) => to_uint (output{1}.[k]) = nth witness base_w{2} k
).
(* First subgoal of while *)
if.
(* First subgoal of if *)
auto => /> *. smt.
(* 2nd+3rd subgoals of if *)
auto => /> *.
do split.
    - smt(@W64).
    - smt(@W64).
    - smt(plus_one).
    - rewrite logw //.
    - smt(@W64).
    - smt.
    - smt(plus_one).
    - smt(@W64).
    - smt.
    - smt(plus_one).
    - auto => /> *. rewrite logw. rewrite w_val //=. smt(shr_base_w).
    - smt(@W64).
    - smt.
    - auto => /> *. do split.
        - smt(@W64).
        - smt(@W64).
        - smt.
        - rewrite logw. smt.       
        - smt(plus_one). 
        - auto => /> *. rewrite logw. rewrite w_val //=. smt(shr_base_w_2).
        - smt(@W64).
        - smt.
(* Last subgoal of while *)
auto => /> *. 
do split.
    - smt().
    - auto => /> *. smt. 
qed.

(*
expand seed :
CORRECTNESS : Auxiliary lemmas with admit
TERMINATION : NOT DONE
*)

lemma e0 (a : int) (b : W64.t):
    a - to_uint b <= 0 => ! (b \ult W64.of_int a).
proof.
admit.
qed.

lemma expand_seed_correctness (outseeds : W8.t Array2144.t, inseed : W8.t Array32.t,
                               pub_seed : W8.t Array32.t, addr : W32.t Array8.t) :
    len = XMSS_WOTS_LEN =>
    equiv [Mp(Syscall).__expand_seed ~ WOTS.pseudorandom_genSK :
    arg{1} = (outseeds, inseed, pub_seed, addr) /\
      arg{2} = (to_list inseed, to_list pub_seed, addr) ==> 
        to_list res{1}.`1 = flatten res{2}].
proof.
rewrite /XMSS_WOTS_LEN.
move => wots_len.
proc.
inline*.
auto => />*.
while (
  len{2} = 67 /\
  ={i}
).
admit.
admit.
qed.


lemma expand_seed_ll : islossless Mp(Syscall).__expand_seed_.
proof.
proc ; inline => //=.
islossless.
while (true) (67 - i) => //= ; last by skip => /#. 
auto => /> *.
islossless ; first by smt().
while (true) (8 - i1) ; last by skip ; auto => /> /#.
auto => /> /#.
while (true) (inlen - (to_uint i0)) => //=; last by skip => /> * ; smt(e0).
auto => /> *. smt.
qed.

(* gen chain *)

lemma b (i : W64.t) (t : int) : ! (i \ult (W64.of_int t)) <=> W64.of_int t \ule i by split ; by smt.
lemma c (i : W64.t) : 64 - to_uint i <= 0 <=> (W64.of_int 64) \ule i by smt.

lemma gen_chain_ll : islossless Mp(Syscall).__gen_chain.
proof.
proc.
islossless.
(* First *)
while (cond = i \ult t /\ i \ult W32.of_int 16) (to_uint (t - i)).
auto => />. 
move => &h H cond.
move : H => [#] a b c d e.
split.
admit.
admit.
admit.
skip => /> *. split. admit.
auto => /> *. admit.
(* Last *)
while (true) ((to_uint inlen) - (to_uint i)).
auto => /> *.
smt(@W64).
skip => /> /#.
qed.

lemma gen_chain_inplace_ll : islossless Mp(Syscall).__gen_chain_inplace.
proof.
proc.
islossless.
while (cond = i \ult t /\ i \ult W32.of_int 16 /\ t = start + steps) (to_uint (t - i)). (* i < (start+steps) && i < XMSS_WOTS_W  *)
auto => /> *.
admit.
admit.
skip.
auto => /> &h *.
split.
admit.
auto => /> i0 H.
pose x := start{h} + steps{h}.
move => ?. admit. (* smt f0 should work but doesnt *)
qed.

(* checksum 
CORRECTNESS : DONE
TERMINATION : DONE
*)
lemma wots_checksum_correctness (msg : W32.t Array67.t) :
    len1 = XMSS_WOTS_LEN1 => 
    w = XMSS_WOTS_W =>
    equiv [Mp(Syscall).__csum ~ WOTS.checksum :
      arg{1} = msg /\ arg{2} = map W32.to_uint (to_list msg) ==> to_uint res{1} = to_uint res{2}].
proof.
rewrite /XMSS_WOTS_LEN_1 /XMSS_WOTS_W ; move => ? ?.
proc => /=.
while (
  i{2} = to_uint i{1} /\
  m{2} = map W32.to_uint (to_list msg_base_w{1}) /\
  0 <= i{2} <= len1
).
auto => /> *.
do split; 1,2,3,4,5: by smt.
auto => /> *.
split; 1: by smt().
auto => /> *. smt.
qed.

lemma csum_ll : islossless Mp(Syscall).__csum.
proof.
proc.
islossless.
while (true) (64 - to_uint i).
auto => /> &h i_lt64.
smt. (* smt(@W64 @Int) fails *)
auto => /> i *.  
rewrite b.
smt(c).
qed.

lemma checksum_ll : islossless Mp(Syscall).__wots_checksum.
proof.
proc.
islossless.
while (true) (to_uint (outlen - consumed)) ; last by skip => /> * ; smt(f0). auto => /> * ; smt(f2).
while (true) (i - aux). auto => /#. skip => /> /#.
while (true) (to_uint ((W64.of_int 64) - i)) ; last by skip => /> ; smt(f0). auto => /> * ; smt(f2).
qed.

(* 
pkgen 
TERMINATION : One subgoal with adimt. I want to apply the lemma gen_chain_inplace_ll
CORRECTNESS :
*)


lemma wots_pkgen_ll : islossless Mp(Syscall).__wots_pkgen.
proof.
proc.
islossless.
- while (true) (67 - i) ; last by skip => /> /#. auto => /> *. admit. (* How do apply trhe lemma gen_chain_inplace_ll here *)
- while (true) (67 - i) ; last by skip => /> /#. auto => /> *. islossless ; first by smt(). while (true) (8 - i) ; last by skip => /> /#. auto => /> *. islossless => /#.
- while (true) (to_uint ((W64.of_int inlen) - i)) ; last by skip => /> * ;  smt(f0). auto => /> * ; smt(f2).
qed.

(*
sign 
TERMINATION : DONE
CORRECTNESS : 
*)
lemma wots_sign_ll : islossless Mp(Syscall).__wots_sign.
proof.
proc.
islossless.
- while (true) (67 - i) ; last by skip => /> /#. auto => /> *. admit. (* How do I apply the lemma gen_chain_inplace_ll here? *)
- while (true) (67 - i) ; last by skip => /> /#. auto => /> *. 
  islossless; first by auto => /> /#. while (true) (8 - i); last by skip => /> /#. auto => /> *. islossless. auto => /> /#.
- while (true) (to_uint ((W64.of_int inlen) - i)) ; last by skip => /> * ; smt(f0). auto => /> *. smt(f2).
- while (true) (to_uint (outlen - consumed)); last by skip => /> ; smt(f0). auto => /> *. smt(f2).
- while (true) (i - aux). auto => /#. skip => /> * ; smt(f1).
- while (true) (to_uint ((W64.of_int 64) - i)); last by skip => /> * ; smt(f0). auto => /> *. smt(f2).
- while (true) (to_uint (outlen - consumed)); last by skip => /> * ; smt(f0). auto => /> *. smt(f2).
qed.

(* 
pk from sig 
TERMINATION : One subgoal with admit
CORRECTNESS :
*)

lemma wots_pk_from_sig_ll : islossless Mp(Syscall).__wots_pk_from_sig.
proof.
proc.
islossless.
- while (true) (67 - i) ; last by skip => /> /#. auto => /> *. islossless ; first by smt().
   - admit. (* cond *)
   - while (true) (to_uint (inlen - i)); last by skip => /> * ; smt(f0). auto => /> *. smt.
- while (true) (to_uint (outlen - consumed)) ; last by skip => /> * ; smt(f0). auto => /> *. smt(f2).
- while (true) (i - aux) ; last by skip => /> /#. auto => /> /#.
- while (true) (to_uint ((W64.of_int 64) - i)) ; last by skip => /> * ; smt(f0). auto => /> ; smt(f2).
- while (true) (to_uint (outlen - consumed)) ; last by skip => /> * ; smt(f0). auto => /> *; smt(f2).
qed.
