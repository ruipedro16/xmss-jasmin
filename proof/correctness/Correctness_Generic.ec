pragma Goals : printall.

require import AllCore List RealExp IntDiv.

from Jasmin require import JModel.

clone import JArray.PolyArray as A.
 
require import Array2 Array3 Array4 Array8 Array32 Array64 Array67 Array128 Array2144.
require import Generic.

require import XMSS_IMPL XMSS_IMPL_PP.

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

lemma list_put_3 ['a] (x : 'a Array3.t) (v : 'a) (i : int) : 
    0 <= i < 3 => put (to_list x) i v = to_list (x.[i <- v]).
proof.
move => [i_ge0 i_lt_3].
apply (eq_from_nth witness).
   - by rewrite size_put !size_to_list.
   - move => j ; rewrite size_put size_to_list. 
    move => [j_ge0 j_lt_3].
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

lemma list_put_67 ['a] (x : 'a Array67.t) (v : 'a) (i : int) : 
    0 <= i < 67 => put (to_list x) i v = to_list (x.[i <- v]).
proof.
move => [i_ge0 i_lt_67].
apply (eq_from_nth witness).
   - by rewrite size_put !size_to_list.
   - move => j ; rewrite size_put size_to_list. 
    move => [j_ge0 j_lt_67].
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

lemma memcpy_2_1 (_out : W8.t Array32.t, _in : W8.t Array2144.t, _in_offset : W64.t) :
    equiv[M(Syscall).__memcpy_u8u8_2_32_2144 ~ Memcpy.__memcpy_u8u8_2 :
      arg{1} = (_out, _in, _in_offset, W64.of_int 32)  /\
      arg{2} = (to_list _out, to_list _in, _in_offset, W64.of_int 32) ==> 
    res{2}.`1 = to_list res{1}.`1 /\ res{1}.`2 = res{2}.`2].
proof.
proc.
auto => /> *.
while(
  0 <= W64.to_uint i{1} <= W64.to_uint bytes{1} /\
  0 <= W64.to_uint bytes{1} /\
  ={bytes, i, in_offset} /\
  in_0{2} = to_list in_0{1} /\
  out{2} = to_list out{1}
) ; last by auto.
auto => /> *.
do split.
    - rewrite to_uintD /#.
    - move => ?. rewrite to_uintD. smt.
    - smt.
qed.

lemma memcpy_2_2 (_out : W8.t Array64.t, _in : W8.t Array2144.t, _in_offset : W64.t) :
    equiv[M(Syscall).__memcpy_u8u8_2_64_2144 ~ Memcpy.__memcpy_u8u8_2 :
      arg{1} = (_out, _in, _in_offset, W64.of_int 64)  /\
      arg{2} = (to_list _out, to_list _in, _in_offset, W64.of_int 64) ==> 
    res{2}.`1 = to_list res{1}.`1 /\ res{1}.`2 = res{2}.`2].
proof.
proc.
auto => /> *.
while(
  0 <= W64.to_uint i{1} <= W64.to_uint bytes{1} /\
  0 <= W64.to_uint bytes{1} /\
  ={bytes, i, in_offset} /\
  in_0{2} = to_list in_0{1} /\
  out{2} = to_list out{1}
) ; last by auto.
auto => /> *.
do split.
    - rewrite to_uintD /#.
    - move => ?. rewrite to_uintD. smt.
    - smt.
qed.

(* Base W *)
lemma base_w_generic_1 (_output : W32.t Array3.t, _input : W8.t Array2.t) :
    equiv[M(Syscall).__base_w_3_2 ~ BaseWGeneric.__base_w :
       arg{1} = (_output, _input) /\ arg{2} = (to_list _output, to_list _input) ==>
    res{2} = to_list res{1}].
proof.
proc.
while (
  0 <= to_uint i{1} <= 3 /\
  ={in_0, bits, total, i} /\
  size output{2} = 3 /\
  input{2} = to_list input{1} /\
  output{2} = to_list output{1}
); auto => /> ; last first.
- split ; by rewrite /to_list size_mkseq.
- move => &1 &2 *. do split.
    + rewrite to_uintD /#.
    + move => ? ; smt(@W64).
    + by rewrite size_put /to_list size_mkseq.
    + apply list_put_3 ; split ; [ smt() | move => ? ; smt ].
    + trivial.
    + move => ?. rewrite size_put /to_list size_mkseq //=.
    + rewrite size_put /to_list size_mkseq //=.
    + move => ?. do split.
      * rewrite to_uintD /#.
      * move => ? ; smt(@W64).
      * by rewrite size_put /to_list size_mkseq.
      * apply list_put_3 ; split ; [ smt() | move => ? ; smt ].
      * move => ?. rewrite size_put /to_list size_mkseq //=.
      * rewrite size_put /to_list size_mkseq //=.
qed.

lemma base_w_generic_2 (_output : W32.t Array67.t, _input : W8.t Array32.t) :
    equiv[M(Syscall).__base_w_67_32 ~ BaseWGeneric.__base_w :
       arg{1} = (_output, _input) /\ arg{2} = (to_list _output, to_list _input) ==>
    res{2} = to_list res{1}].
proof.
proc.
while (
  0 <= to_uint i{1} <= 67 /\
  ={in_0, bits, total, i} /\
  size output{2} = 67 /\
  input{2} = to_list input{1} /\
  output{2} = to_list output{1}
); auto => /> ; last first.
- split ; by rewrite /to_list size_mkseq.
- move => &1 &2 *. do split.
    + rewrite to_uintD /#.
    + move => ? ; smt(@W64).
    + by rewrite size_put /to_list size_mkseq.
    + apply list_put_67 ; split ; [ smt() | move => ? ; smt ].
    + trivial.
    + move => ?. rewrite size_put /to_list size_mkseq //=.
    + rewrite size_put /to_list size_mkseq //=.
    + move => ?. do split.
      * rewrite to_uintD /#.
      * move => ? ; smt(@W64).
      * by rewrite size_put /to_list size_mkseq.
      * apply list_put_67 ; split ; [ smt() | move => ? ; smt ].
      * move => ?. rewrite size_put /to_list size_mkseq //=.
      * rewrite size_put /to_list size_mkseq //=.
qed.
