pragma Goals : printall.

require import AllCore List RealExp IntDiv.

from Jasmin require import JModel.

(*
require import Params Notation Parameters Address Primitives Wots.
require import XMSS_IMPL XMSS_IMPL_PP Parameters.
*)
 
require import Array2 Array3 Array4 Array8 Array32 Array64 Array67 Array128 Array2144.
require import Generic.

clone import JArray.PolyArray as A.

(********************)
(* Auxiliary Lemmas *)
(********************)

lemma list_put ['a] (x : 'a A.t) (v : 'a) (i : int) :
    0 <= i < A.size => put (to_list x) i v = to_list (x.[i <- v]).
proof.
move=> [i_ge0 i_lt_size] ; apply/(eq_from_nth witness).
- by rewrite size_put !size_to_list.
move=> j; rewrite size_put size_to_list => -[j_ge0 j_lt_size].
rewrite get_to_list get_setE // nth_put 1:size_to_list //.
by rewrite [j=i]eq_sym.
qed.

lemma list_put_32 ['a] (x : 'a Array32.t) (v : 'a) (i : int) :
    0 <= i < 32 => put (to_list x) i v = to_list (x.[i <- v]).
proof.
move => [i_ge0 i_lt_32].
apply (eq_from_nth witness).
  - by rewrite size_put !size_to_list.
  - move => j. rewrite size_put size_to_list. move => [j_ge0 j_lt_32].
    rewrite get_to_list get_setE //. 
    rewrite nth_put 1:size_to_list //.
    by rewrite [j=i]eq_sym.
qed.

lemma list_put_64 ['a] (x : 'a Array64.t) (v : 'a) (i : int) : 
    0 <= i < 64 => put (to_list x) i v = to_list (x.[i <- v]).
proof.
move => [i_ge0 i_lt_64].
apply (eq_from_nth witness).
  - by rewrite size_put !size_to_list.
  - move => j ; rewrite size_put size_to_list. 
    move => [j_ge0 j_lt_64].
    rewrite get_to_list get_setE //.
    rewrite nth_put 1:size_to_list //.
    by rewrite [j=i]eq_sym.
qed.

lemma list_put_4 ['a] (x : 'a Array4.t) (v : 'a) (i : int) : 
    0 <= i < 4 => put (to_list x) i v = to_list (x.[i <- v]).
proof.
move => [i_ge0 i_lt_4].
apply (eq_from_nth witness).
   - by rewrite size_put !size_to_list.
   - move => j ; rewrite size_put size_to_list. 
    move => [j_ge0 j_lt_4].
    rewrite get_to_list get_setE //.
    rewrite nth_put 1:size_to_list //.
    by rewrite [j=i]eq_sym.
qed.

lemma list_put_128 ['a] (x : 'a Array128.t) (v : 'a) (i : int) : 
    0 <= i < 128 => put (to_list x) i v = to_list (x.[i <- v]).
proof.
move => [i_ge0 i_lt_128].
apply (eq_from_nth witness).
  - by rewrite size_put !size_to_list.
  - move => j ; rewrite size_put size_to_list. 
    move => [j_ge0 j_lt_128].
    rewrite get_to_list get_setE //.
    rewrite nth_put 1:size_to_list //.
    by rewrite [j=i]eq_sym.
qed.

(**********************************************************************************************************************)

require import XMSS_IMPL XMSS_IMPL_PP.

lemma memcpy_64 (output : W8.t Array64.t, input : W8.t Array64.t) :
    equiv [ M(Syscall).__memcpy_u8u8_64_64 ~ Memcpy._x_memcpy_u8u8 :
            arg{1}=(output,input) /\ 
            arg{2}=(to_list output, to_list input) ==> 
            res{2} = to_list res{1} ].
proof.
proc.
while (
  size in_0{2} = 64 /\ ={i} /\ 
  out{2} = to_list out{1} /\ in_0{2} = to_list in_0{1} /\
  0 <= to_uint i{1} <= 64
) ; auto => /> ; last first. 
    - split ; by rewrite size_to_list //.
    - move => * ; do split.
        + rewrite list_put_64 //. split ; [ assumption | smt(@W64) ].
        + smt(W64.to_uint_cmp).
        + smt(@W64).
        + rewrite size_to_list. smt(@W64).
        + smt(@W64).
qed.

lemma memcpy_32 (output : W8.t Array32.t, input : W8.t Array32.t) :
    equiv [ M(Syscall).__memcpy_u8u8_32_32 ~ Memcpy._x_memcpy_u8u8 :
            arg{1}=(output,input) /\ 
            arg{2}=(to_list output, to_list input) ==> 
            res{2} = to_list res{1} ].
proof.
proc.
while (
  size in_0{2} = 32 /\ ={i} /\ 
  out{2} = to_list out{1} /\ in_0{2} = to_list in_0{1} /\
  0 <= to_uint i{1} <= 32
) ; auto => /> ; last first. 
    - split ; by rewrite size_to_list //.
    - move => * ; do split.
        + rewrite list_put_32 //. split ; [ assumption | smt(@W64) ].
        + smt(W64.to_uint_cmp).
        + smt(@W64).
        + rewrite size_to_list. smt(@W64).
        + smt(@W64).
qed.

lemma memcpy_64_32 (output : W8.t Array64.t, input : W8.t Array32.t) :
    equiv [ M(Syscall).__memcpy_u8u8_64_32 ~ Memcpy._x_memcpy_u8u8 :
            arg{1}=(output,input) /\ 
            arg{2}=(to_list output, to_list input) ==> 
            res{2} = to_list res{1} ].
proof.
proc.
while (
  size in_0{2} = 32 /\ ={i} /\ 
  out{2} = to_list out{1} /\ in_0{2} = to_list in_0{1} /\
  0 <= to_uint i{1} <= 32
) ; auto => /> ; last first. 
    - split ; by rewrite size_to_list //.
    - move => * ; do split.
        + rewrite list_put_64 //. split ; [ assumption | smt(@W64) ].
        + smt(W64.to_uint_cmp).
        + smt(@W64).
        + rewrite size_to_list. smt(@W64).
        + smt(@W64).
qed.

(* Memcpy_ptr *)

require import Utils.
lemma memcpy_ptr_32 (output : W8.t Array32.t, _offset : W64.t, 
                     in_ptr : W64.t, _inlen : W64.t) :
    equiv [ M(Syscall).__memcpy_u8u8p_32 ~ Memcpy._x_memcpy_u8u8p :
            0 <= to_uint _inlen <= 32 /\ ={Glob.mem} /\
            arg{1} = (output, _offset, in_ptr, _inlen) /\
            arg{2} = (to_list output, _offset, in_ptr, _inlen) ==>
            res{2}.`1 = to_list res{1}.`1].
proof.
proc.
while (
  ={i, offset, Glob.mem, in_0} /\
  0 <= to_uint i{1} <= to_uint inlen{1} /\
  0 <= to_uint offset{1} <= to_uint inlen{1} /\
  out{2} = to_list out{1}
); auto => />.
move => &1 &2 H0 H1 H2 H3 H4 H5.
do split.
    - smt(@W64).
    - smt(@W64).
    - smt(@W64).
    - admit.
    - pose x := out{1}.
    - move => ? ; smt(@W64).

lemma memcpy_ptr_32 (_out : W8.t Array32.t, _in : W64.t, _inlen : W64.t) :
    0 < to_uint _inlen <= 32 =>
    equiv[M(Syscall).__memcpy_u8u8p_32 ~ Memcpy._x_memcpy_u8u8p :
      arg{1} = (_out, W64.zero, _in, _inlen) /\ 
      arg{2} = (to_list _out, W64.zero, _in, _inlen) /\
      ={Glob.mem} ==> 
         res{2}.`1 = to_list res{1}.`1 /\ res{1}.`2 = res{2}.`2].
proof.
move => [inlen_g0 inlen_lt_32].
proc.
while(
  inlen{1} = _inlen /\
  ={i, offset, inlen, Glob.mem, in_0} /\
  0 <= to_uint i{1} <= to_uint inlen{1} /\
  out{2} = to_list out{1} /\
  offset{1} = i{1}
) ; auto => /> ; last by smt().
move => &1 &2 H0 H1 H2.
do split.
    - smt(W64.to_uint_cmp).
    - move => ?. rewrite to_uintD_small //= /#.
    - rewrite list_put_32 //. split. assumption. move => ?. smt.
qed.

lemma memcpy_ptr_32 (_out : W8.t Array32.t, _offset : W64.t, _in : W64.t, _inlen : W64.t) :
    0 <= to_uint _offset /\ 
    0 <= to_uint _inlen <= 32
    => 
    equiv[M(Syscall).__memcpy_u8u8p_32 ~ Memcpy._x_memcpy_u8u8p :
      arg{1} = (_out, _offset, _in, _inlen) /\ 
      arg{2} = (to_list _out, _offset, _in, _inlen) /\
      ={Glob.mem} ==> 
         res{2}.`1 = to_list res{1}.`1 /\ res{1}.`2 = res{2}.`2].
proof.
move => [offset_ge0 t].
move : t => [#] inlen_ge0 inlen_lte_32.
proc.
while(
  ={i, offset, inlen, Glob.mem, in_0} /\
  inlen{1} = _inlen /\
  to_uint _offset <= to_uint offset{1} /\
  0 <= to_uint i{1} <= to_uint inlen{1} /\
  out{2} = to_list out{1}
) ; auto => />.
move => &1 &2 H0 H1 H2 H3.
do split.
    - admit.
    - rewrite to_uintD_small /#.
    - admit.
    - rewrite list_put_32 //. split ; by admit.

    - smt(W64.to_uint_cmp).
    - rewrite to_uintD_small /#.
    - rewrite list_put_32 //. split. idtac.
qed.

(* Memset *)
lemma memset_4 (_a : W8.t Array4.t) (_value : W8.t) :    
    equiv [ M(Syscall).__memset_u8_4 ~ Memset.memset_u8 : 
            arg{1} = (_a, _value) /\ arg{2} = (to_list _a, W64.of_int 4, _value) ==>
            res{2} = to_list res{1}].
proof.
proc.
while (
  0 <= to_uint i{1} <= 4 /\ inlen{2} = W64.of_int 4 /\ ={i, value} /\ a{2} = to_list a{1}
) ; auto => />.
move => &1 &2 H0 H1 H2.
do split ; last first.
    - rewrite list_put_4 ;  split ; [ assumption | move => ? ; smt ].
    - rewrite to_uintD_small /#.
    - move => ?. rewrite to_uintD_small ; smt(@W64).
qed.

lemma memset_128 (_a : W8.t Array128.t) (_value : W8.t) :    
    equiv [ M(Syscall).__memset_u8_128 ~ Memset.memset_u8 : 
            arg{1} = (_a, _value) /\ arg{2} = (to_list _a, W64.of_int 128, _value) ==>
            res{2} = to_list res{1}].
proof.
proc.
while (
  0 <= to_uint i{1} <= 128 /\ inlen{2} = W64.of_int 128 /\ ={i, value} /\ a{2} = to_list a{1}
) ; auto => />.
move => &1 &2 H0 H1 H2.
do split ; last first.
    - rewrite list_put_128 ;  split ; [ assumption | move => ? ; smt ].
    - rewrite to_uintD_small /#.
    - move => ?. rewrite to_uintD_small ; smt(@W64).
qed.



(* Base W *)
