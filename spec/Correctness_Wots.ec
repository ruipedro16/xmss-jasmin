pragma Goals : printall.

require import AllCore List RealExp IntDiv.
from Jasmin require import JModel.
require import Notation Parameters Address Primitives Wots.
require import XMSS_IMPL XMSS_IMPL_PP.
require import Generic.
require import Array2 Array3 Array8 Array32 Array67 Array2144.

axiom array3_list_put ['a] (x : 'a Array3.t) (v : 'a) (i : int) : put (to_list x) i v = to_list (x.[i <- v]).
axiom array67_list_put ['a] (x : 'a Array67.t) (v : 'a) (i : int) : put (to_list x) i v = to_list (x.[i <- v]).

lemma zero (x : int) :
    W64.of_int x = W64.zero => x = 0.
proof.
case (x = 0).
move => ?.
smt(@W64).
move => ?.
rewrite implybF.
admit.
qed.

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

lemma base_w_correctness(_out : W32.t list, _outlen : W64.t, _input : W8.t list) :
    0 < to_uint _outlen =>
    w = 16 => (* FIXME: How do I this correctly: This is implementation-specific *)
    equiv[BaseWGeneric.__base_w ~ BaseW.base_w :
      arg{1} = (_out, _outlen, _input) /\ 
      arg{2} = (_input, to_uint _outlen) ==> 
        res{1} = map (fun (x : int) => W32.of_int x) res{2}
    ]. 
proof.
move => ? ?.
proc.
auto => /> *.
while(
    outlen{1} = W64.of_int outlen{2} /\
    input{1} = X{2} /\
    in_0{1} = W64.of_int _in{2} /\
    out{1} = W64.of_int out{2} /\
    consumed{1} = W64.of_int consumed{2} /\
    bits{1} = W64.of_int bits{2} /\
    ={total} /\
    0 <= consumed{2} <= outlen{2} /\
    0 <= out{2} <= outlen{2} /\
    0 <= _in{2} <= consumed{2} /\
    out{2} = consumed{2}
).
(* 1st subgoal of while *)
if.
(* 1st subgoal of if *)
auto => /> *.
smt(zero).
(* 2nd subgoal of if *)
auto => /> *.
do split.
admit.
admit.
admit.
congr.
smt.
smt.
smt.
smt.
(* 3rd subgoal of if *)
auto => /> *.
do split.
admit.
admit.
admit.
admit.
(* 2nd subgoal of while *)
auto => /> *.
do split.
smt(@W64).
smt(@W64).
smt(@W64).
qed.


lemma wots_checksum(csum_base_w : W32.t Array3.t, msg_base_w : W32.t Array67.t) :
    hoare[Mp(Syscall).__wots_checksum :
      arg = (csum_base_w, msg_base_w) ==> true].
proof.
proc.
admit.
qed.

