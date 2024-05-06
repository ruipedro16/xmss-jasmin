pragma Goals : printall.

require import AllCore List RealExp IntDiv.
require Subtype. 

from Jasmin require import JModel.

require import Notation Parameters Address Primitives Wots.

import NBytes.
import Array8.

require import XMSS_IMPL.

(*
    We first prove that the equivalence between the extracted EC and the preprocessed EC
    We then prove that the preprocessed EC is equivalent to the specification (so the extracted EC is also equivalent to the spec)
*)

require import Array2 Array3 Array32 Array67.

module BaseWGeneric = {
  proc __base_w (output : W32.t list, input : W8.t list) : W32.t list = {

    var in_0:W64.t;
    var out:W64.t;
    var bits:W64.t;
    var consumed:W64.t;
    var total:W8.t;
    var total_32:W32.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var  _0:bool;

    var inlen : W64.t <- W64.of_int (size input);
    var outlen : W64.t <- W64.of_int (size output);

    in_0 <- W64.zero;
    out <- W64.zero;
    bits <- W64.zero;
    consumed <-W64.zero;

    while ((consumed \ult outlen)) {
      if (bits = W64.zero) {
        total <- input.[(W64.to_uint in_0)];
        in_0 <- (in_0 + (W64.of_int 1));
        bits <- (bits + (W64.of_int 8));
      }
      
      bits <- (bits - (W64.of_int 4));
      total_32 <- (zeroextu32 total);
      (_of_, _cf_, _sf_,  _0, _zf_, total_32) <- SHR_32 total_32 (truncateu8 bits);
      total_32 <- (total_32 `&` (W32.of_int (16 - 1)));
      output <- put output (W64.to_uint out) total_32; (* output.[(W64.to_uint out)] <- total_32; *)
      out <- (out + (W64.of_int 1));
      consumed <- (consumed + (W64.of_int 1));
    }

    return (output);
  }
}.

lemma base_w_generic_1 (output : W32.t Array3.t, input : W8.t Array2.t) :
    let _output : W32.t list = mkseq (fun i => output.[i]) 3 in
    let _input  : W8.t list = mkseq (fun i => input.[i]) 2 in
    size _output = 3 /\ size _input = 2 =>
    equiv[M(Syscall).__base_w_3_2 ~ BaseWGeneric.__base_w :
       arg{1} = (output, input) /\
       arg{2} = (_output, _input) ==> 
      mkseq (fun i => res{1}.[i]) 3 = res{2}].
proof.
move => *.
progress.
proc.
auto => /> *.
while (
  consumed{1} = consumed{2} /\ 
  inlen{2} = W64.of_int 2 /\ outlen{2} = W64.of_int 3 /\
  (forall (k : int), 0 <= k < W64.to_uint inlen{2} => input{1}.[k] = input{2}.[k]) /\
  (forall (k : int), 0 <= k < 3 => output{1}.[k] = output{2}.[k])
).
- auto. (* This solves the first subgoal generated by while *)
- auto => /> *. progress. (* progress generates 4 subgoals *)
    - smt().
    - smt().
    - smt. (* FIXME: How to use assumption H when I call smt? smt() fails but smt(H) doesnt work *)
    - admit.
qed.

lemma base_w_generic_2 (output : W32.t Array67.t, input : W8.t Array32.t):
    let _output = mkseq (fun i => output.[i]) 67 in
    let _input  = mkseq (fun i => input.[i]) 32 in 
    size _output = 67 /\ size _input = 32 =>
    equiv[M(Syscall).__base_w_67_32 ~ BaseWGeneric.__base_w :
       arg{1} = (output, input) /\
       arg{2} = (_output, _input) ==> 
      mkseq (fun i => res{1}.[i]) 67 = res{2}].
proof.
move => *.
progress.
proc.
auto => /> *.
while (
  consumed{1} = consumed{2} /\
  inlen{2} = W64.of_int 32 /\ outlen{2} = W64.of_int 67 /\
  (forall (k : int), 0 < k < W64.to_uint inlen{2} => input{1}.[k] = input{2}.[k]) /\
  (forall (k : int), 0 < k < W64.to_uint outlen{2} => output{1}.[k] = output{2}.[k])
).
- auto. (* This solves the first subgoal generated by while *)
- auto => /> *. progress. (* progress generates 4 subgoals *)
    - smt().
    - smt().
    - smt. (* FIXME: How to use assumption H when I call smt? smt() fails but smt(H) doesnt work *)
    - admit. (* FIXME: *)
qed.
