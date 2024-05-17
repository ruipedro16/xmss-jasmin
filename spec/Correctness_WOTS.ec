pragma Goals : printall.

require import AllCore List RealExp IntDiv.
from Jasmin require import JModel.
require import Notation Parameters Address Primitives Wots.
require import XMSS_IMPL.
require import Generic.
require import Array2 Array3 Array8 Array32 Array67.

axiom array3_list_put ['a] (x : 'a Array3.t) (v : 'a) (i : int) : put (to_list x) i v = to_list (x.[i <- v]).

axiom array67_list_put ['a] (x : 'a Array67.t) (v : 'a) (i : int) : put (to_list x) i v = to_list (x.[i <- v]).

lemma list_array_mkseq (a : W8.t Array2.t) : 
    let b = mkseq (fun (i : int) => a.[i]) 2 in
    forall (i : int), 0 <= i < 2 => a.[i] = b.[i] by smt(@List @Array2).


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

(***************************************************************************************)


lemma wots_checksum(csum_base_w : W32.t Array3.t, msg_base_w : W32.t Array67.t) :
    hoare[M(Syscall).__wots_checksum :
      arg = (csum_base_w, msg_base_w) ==> true].
proof.
proc.
admit.
qed.

(***************************************************************************************)


(* This lemma states that the the generic version of base_w (which is/will be proved above that is equivalent to the one extracted from the Jasmin impl) is correct with respect to the specification *)
lemma base_w_impl_spec (input : byte list, outlen : int) :
    let t : W32.t list = nseq outlen W32.zero in
    size t = outlen => 
    equiv[BaseW.base_w ~ BaseWGeneric.__base_w :
      arg{1} = (input, outlen) /\
      arg{2} = (t, input) ==> 
    map W32.of_int res{1} = res{2}].
proof.
move => *.
proc.
auto => /> *.
while(
  input{1} = input{2} /\ total{1} = total{2}
).
admit. (* TODO: *)
qed.
