pragma Goals : printall.

require import AllCore List RealExp IntDiv.
require import XMSS_IMPL XMSS_IMPL_PP Generic.

from Jasmin require import JModel.

(* Auxiliary Lemmas *)
(* NOTE: Lemmas with admit are annotated with nosmt *)

lemma lemma_1 (a b : int) :
    a - b <= 0 => ! (b < a) by smt().

lemma lemma_2 (a : int) (b : W64.t) :
    0 <= a < W64.max_uint => 
    a - to_uint b <= 0 => ! (b \ult W64.of_int a) by smt(@W64). 

lemma lemma_3 (a : W64.t) (b : int) :
    0 <= b < W64.max_uint => 
    b - to_uint a <= 0 => ! (a \ult W64.of_int b) by smt(@W64).

lemma nosmt lemma_4 (a b : W64.t) :
    a - b \ule W64.zero => ! (b \ult a).
proof.
admit. (* smt(@W64). fails *)
qed.

lemma nosmt lemma_5 (a b : W64.t) : 
    to_uint (a - (b + W64.one)) < to_uint (a - b).
proof.    
admit.
qed.

lemma lemma_5_int (a b : int) : a - (b + 1) < (a - b) by smt().
lemma lemma_6_int (a b : int) : a - (b + 1) < a - b by smt().

lemma nosmt lemma_6_W32 (a b : W32.t) :
    to_uint a - to_uint (b + W32.one) < to_uint a - to_uint b.
proof.
admit. (* smt(@W32 lemma_6_int). *)
qed.

lemma nosmt lemma_6_W64 (a b : W64.t) :
    to_uint a - to_uint (b + W64.one) < to_uint a - to_uint b.
proof.
admit. (* smt(@W32 lemma_6_int). *)
qed.

lemma nosmt lemma_7 (a : int) (b : W64.t) : a - to_uint (b + W64.one) < a - to_uint b.
proof.
do rewrite /to_uint => //=.
admit.
qed.

lemma lemma_8 (b : W64.t) : 32 - to_uint b <= 0 => ! (b \ult (of_int 32)%W64) by smt(@W64).
lemma lemma_9 (a : W64.t) : 64 - to_uint a <= 0 => ! (a \ult (of_int 64)%W64) by smt(@W64).

lemma nosmt lemma_10 (a : int) (b : W64.t) :
    a - to_uint (b + W64.one) < a - to_uint b.
proof.
admit. (* smt(@W64). *)
qed.

lemma lemma_11 (a b : W64.t) : to_uint a - to_uint b <= 0 => ! (b \ult a) by smt(@W64).
lemma nosmt lemma_12 (a : W64.t) : 64 - to_uint (a + W64.one) < 64 - to_uint a.
proof.
rewrite /to_uint /W64.one.
simplify.
admit.
qed.

lemma nosmt lemma_13 (a : int) (b : W64.t) : 
    0 < a < W64.max_uint =>
    a - to_uint (b + W64.one) < a - to_uint b. 
proof.
admit. (*  smt(@W64) fails *)
qed.

lemma nosmt lemma_14 (a : int) (b : W64.t) : a - to_uint b <= 0 => ! (b \ult (of_int a)%W64).
proof.
admit. (* smt(@W64). *)
qed.

lemma lemma_15 (a : W64.t) : 
    a \ult (of_int 32)%W64 => 32 - to_uint (a + W64.one) < 32 - to_uint a by smt.

(* Base w *)

lemma base_w_ll : islossless BaseWGeneric.__base_w.
proof.
proc.
islossless.
while (true) ((to_uint outlen) - (to_uint consumed)) ; [auto => /> *; smt(@W64) | skip => /> /#].
qed.

(*
lemma base_w_ll (output : W32.t list, outlen : W64.t, input : W8.t list): 
    W64.zero \ule outlen =>
    phoare [BaseWGeneric.__base_w : arg=(output, outlen, input) ==> true] = 1%r.
proof.
move => outlen_ge0.
proc.
while (W64.zero \ule consumed{hr} /\ W64.zero \ule outlen{hr}) (to_uint (outlen - consumed)).
auto => /> *. 
do split ; [ smt(@W64) | smt(lemma_5) ]. (* lemma_5 is not proved *)
(* Second subgoal *)
auto => /> * ; smt(@W64).
qed.
*)

(* Gen Chain *)
lemma gen_chain_ll : islossless Mp(Syscall).__gen_chain.
proof.
proc ; inline*.
islossless.
  - while (true) ((to_uint t) - (to_uint i)) ; last by skip => /> * ; smt(@W64).
    auto => />. islossless ; first by auto => /> ; smt(lemma_6_W32).
      - while (true) (32 - to_uint i1) ; [auto => /> * ; smt(lemma_10) | skip => /> * ; smt(lemma_8)].
      - while (true) (8 - i4) ; [auto => /# | skip => /> /#].
      - while (true) (8 - i3) ; [auto => /# | skip => /> /#].
      - while (true) (i2 - aux0) ; [auto => /> /# | skip => /> /#].
  - while (true) ((to_uint inlen) - (to_uint i0)) ; [auto => /> * ; smt(lemma_6_W64) | skip => /> * ; smt(lemma_11)].
qed.

lemma gen_chain_inplace_ll : islossless Mp(Syscall).__gen_chain_inplace.
proof.
proc ; inline*.
islossless.
while (true) ((to_uint t) - (to_uint i)) ; last by skip => /> /#.
auto => /> *. 
islossless.
  - auto => /> ; smt(lemma_6_W32).
  - while (true) (32 - to_uint i0) ; [auto => /> * ; smt(lemma_7) | skip => /> * ; smt(@W64)].
  - while (true) (8 - i3) ; [auto => /> * ; smt(@W64) | skip => /> /#].
  - while (true) (8 - i2) ; [auto => /> /# | skip => /> /#].
  - while (true) (i1 - aux0) ; [auto => /# | skip => /> /#].
qed.

(* Checksum *)
lemma csum_ll : islossless Mp(Syscall).__csum.
proof.
proc.
while (0 <= to_uint i <= 64) (64 - to_uint i); auto => />.
  - move => &hr. rewrite ultE of_uintK /= => *. rewrite to_uintD_small => /#.
  - move => ?. rewrite ultE => /= /#. 
qed.

lemma checksum_ll : islossless Mp(Syscall).__wots_checksum.
proof.
proc.
islossless.
  - while (true) ((to_uint outlen) - (to_uint consumed)) ; [auto => /> * ; smt(lemma_6_W64) | skip => /> * ; smt(lemma_11)].
  - while (true) (i - aux) ;  [auto => /> /# | skip => /#].
  - while (true) (64 - to_uint i) ; [auto => /> * ; smt(lemma_12) | skip => /> ; smt(@W64)].
qed.

(* Expand Seed *)
lemma expand_seed_ll : islossless Mp(Syscall).__expand_seed_.
proof.
proc ; inline*.
islossless.  
  - while (true) (67 - i); last by skip => /> /#. auto => /> *. while (true) (8 - i1) ; by auto => /> /#.
  - while (true) (inlen - to_uint i0) ; [auto => /> * ; apply lemma_10 | skip => /> * ; smt(lemma_14)].
qed.

(* Pk Gen *)
lemma pkgen_ll : islossless Mp(Syscall).__wots_pkgen.
proof.
proc ; inline*.
islossless.
(* 1 *)
  - while (true) (67 - i) ; last by skip => /> /#. auto => /> *. islossless ; first by auto => /#.
    - while (true) ((to_uint t) - (to_uint i1)) ; last by skip => /> * ; smt(lemma_11). auto => /> *. islossless.
        - auto => /> * ; smt(lemma_6_W32).
        - while (true) (32 - to_uint i4) ; [auto => /> * ; smt(lemma_15) | skip => /> * ; smt(lemma_8)].
        - while (true) (8 - i7) ; [auto => /> /# | skip => /> /#].
        - while (true) (8 - i6) ; [auto => /> /# | skip => /> /#].
        - while (true) (i5 - aux3) ; [auto => /> /# | skip => /> /#].
(* 2 *) 
  - while (true) (67 - i0) ; last by skip => /> /#. auto =>  /> *. islossless ; first by smt().
    while (true) (8 - i3) ; [auto => /> /# | skip => /> /#].
(* 3 *)
  - while (true) (inlen - to_uint i2); [auto => /> * ; smt(lemma_6_W64) | skip => /> * ; smt(lemma_14)].
qed.

(* Sign *)
lemma wots_sign_ll : islossless Mp(Syscall).__wots_sign.
proof.
proc ; inline*.
islossless.
(* 1 *)
- while (true) (67 - i); last by skip => /> /#. auto => /> *. islossless; first by auto => /> /#.
  while (true) ((to_uint t) - (to_uint i0)) ; last by skip => /> /#. auto => /> *. islossless.
  - auto => /> * ; smt(lemma_6_W32).
  - while (true) (32 - to_uint i4) ; [auto => /> * ; smt(lemma_7) | skip => /> * ; smt(lemma_8)].
  - while (true) (i9 - 8); by admit.
  - idtac. (* FIX HERE *)
  - while (true) (i7 - aux4) ; by auto => /> /#.
(* 2 *)
- while (true) (67 - i1); last by skip => /#. auto => /> *. islossless; first by auto => /> /#.
  while (true) (8 - i3) ; [auto => /> /# | skip => /> /#].
(* 3 *)
- while (true) (inlen - to_uint i2) ; [auto => /> * ; smt(lemma_10) | skip => /> * ; smt(lemma_14)].
(* 4 *)
- while (true) ((to_uint outlen1) - (to_uint consumed0)) ;  [auto => /> * ; smt(lemma_6_W64) | skip => /> * ; smt(lemma_11)].
(* 5 *)
-  while (true) (i6 - aux3) ; [auto => /> /# | skip => /#].
(* 6 *)
- while (true) (64 - to_uint i5) ; [auto => /> * ; smt(lemma_12) | skip => /> * ; smt(lemma_9)].
(* 7 *)
- while (true) ((to_uint outlen) - (to_uint consumed)) ; [auto => /> * ; smt (lemma_6_W64) | skip => /> * ; smt(lemma_11)].
qed.

(* Pk from Sig *)
lemma wots_pk_from_sig_ll : islossless Mp(Syscall).__wots_pk_from_sig.
proof.
proc ; inline*.
admit.
qed.
