
(*********************************************************************************************)
(************************************* MEMCPY_2 **********************************************)
(*********************************************************************************************)

(*
       $ grep -nr "proc __memcpy_u8u8_2_" extraction/XMSS_IMPL.ec

       proc __memcpy_u8u8_2_32_2144 (out:W8.t Array32.t, out_offset:W64.t, => Always called with bytes = 32
       proc __memcpy_u8u8_2_64_2144 (out:W8.t Array64.t, out_offset:W64.t, => Always called with bytes = 2 * 32
*)

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
smt.
smt.
smt.
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
smt.
smt.
smt.
qed.
