pragma Goals : printall.

require import AllCore List RealExp IntDiv.
from Jasmin require import JModel.

require import XMSS_IMPL.

require import Generic.

require import Array4 Array32 Array64 Array96 Array128 Array2144.

lemma list_array_size_32 (x : W8.t Array32.t) :
    let y : W8.t list = mkseq (fun (i : int) => x.[i]) 32 in
    size y = 32.
proof.
move => y ; smt(@List).
qed.

axiom array4_list_put  ['a] (x : 'a Array4.t)  (v : 'a) (i : int) : put (to_list x) i v = to_list (x.[i <- v]).
axiom array32_list_put_ ['a] (x : 'a Array32.t) (v : 'a) (i : int) : put (to_list x) i v = to_list (x.[i <- v]).
axiom array64_list_put_ ['a] (x : 'a Array64.t) (v : 'a) (i : int) : put (to_list x) i v = to_list (x.[i <- v]).
axiom array128_list_put ['a] (x : 'a Array128.t) (v : 'a) (i : int) : put (to_list x) i v = to_list (x.[i <- v]).

(* Adding 1 to a positive number yields a positive number *)
lemma add_1_W64 (x : W64.t) :
    0 < W64.to_uint x => 0 < (W64.to_uint x) + 1 by smt(@W64).

pred list_array_eq (x : W8.t Array32.t, y : W8.t list) =
  size y = 32 /\ forall (k : int), 0 <= k < 32 => x.[k] = y.[k].

pred list_array_eq_64 (x : W8.t Array64.t, y : W8.t list) =
  size y = 64 /\ forall (k : int), 0 <= k < 64 => x.[k] = y.[k].

(* This is not used I think *)
lemma array32_list_put (x : W8.t Array32.t, y : W8.t list, t : W8.t, i : int) :
    list_array_eq x y => list_array_eq x.[i <- t] (put y i t).
proof.
rewrite /list_array_eq.
move => H.
split ; [smt(@List) | progress ; smt(@List @Array32)].
qed.

lemma list_array_size_64 (x : W8.t Array64.t) :
    let y : W8.t list = mkseq (fun (i : int) => x.[i]) 64 in
    size y = 64.
proof.
move => y ; smt(@List).
qed.

lemma size_ge0_W64 ['a] (x : 'a list) : W64.to_uint(W64.zero) <= size x by smt.

(*********************************************************************************************)
(************************************* MEMCPY ************************************************)
(*********************************************************************************************)

lemma memcpy_32 (out : W8.t Array32.t, offset : W64.t, in_0 : W8.t Array32.t) :
    (* inlen = 32 /\ outlen = 32 *)
    let _out : W8.t list = mkseq (fun i => out.[i]) 32 in
    let _in : W8.t list = mkseq (fun i => in_0.[i]) 32 in
    size _out = 32 /\ size _in = 32 /\ offset = W64.zero  => 
    equiv [M(Syscall).__memcpy_u8u8_32_32 ~ Memcpy._x_memcpy_u8u8 :
      arg{1} = (out, W64.zero, in_0) /\
      arg{2} = (_out, 32, W64.zero, _in, 32) ==> 
    forall (i : int), 0 <= i < 32 => out{1}.[i] = out{2}.[i]].
proof.
move => H0 H1 H3.
proc.
auto => /> *.
while (
  inlen{2} = 32 /\
  0 <= W64.to_uint i{1} <= 32 /\
  0 <= W64.to_uint offset{1} <= 32 /\
  ={i, offset} /\
    list_array_eq in_0{1} H1 /\
  forall (k : int), 0 <= k < W64.to_uint i{1} => out{1}.[k] = out{2}.[k]
).
auto => />.
progress.
smt(@W64).
smt.
auto => /> *. 
progress by smt. 
qed.

lemma memcpy_64 (out : W8.t Array64.t, offset : W64.t, in_0 : W8.t Array64.t) :
    (* inlen = 64 /\ outlen = 64 *)
    let _out : W8.t list = mkseq (fun i => out.[i]) 64 in
    let _in : W8.t list = mkseq (fun i => in_0.[i]) 64 in
    size _out = 64 /\ size _in = 64 /\ offset = W64.zero => 
    equiv [M(Syscall).__memcpy_u8u8_64_64 ~ Memcpy._x_memcpy_u8u8 :
      arg{1} = (out, W64.zero, in_0) /\
      arg{2} = (_out, 64, W64.zero, _in, 64) ==> 
    forall (i : int), 0 <= i < 64 => out{1}.[i] = out{2}.[i]].
proof.
move => H0 H1 H2.
proc.
auto => /> *.
while (
  inlen{2} = 64 /\
  0 <= W64.to_uint i{1} <= 64 /\
  0 <= W64.to_uint offset{1} <= 64 /\
  ={i, offset} /\
    list_array_eq_64 in_0{1} H1 /\
  forall (k : int), 0 <= k < W64.to_uint i{1} => out{1}.[k] = out{2}.[k]
).
auto => /> ; progress.
smt(@W64).
smt. 
auto => /> * ; progress by smt.
qed.

lemma memcpy_128_32 (out : W8.t Array128.t, offset : W64.t, in_0 : W8.t Array32.t) :
    (* inlen = 32 /\ outlen = 128 *)
    (* offset + inlen <= outlen   *)
    (* offset <= outlen - inlen   *)
    let _out : W8.t list = mkseq (fun i => out.[i]) 128 in
    let _in : W8.t list = mkseq (fun i => in_0.[i]) 32 in
    let outlen = size _out in
    let inlen = size _in in
    outlen = 128 /\ inlen = 3 /\ 0 <= W64.to_uint offset <= (outlen - inlen) => 
    equiv [M(Syscall).__memcpy_u8u8_128_32 ~ Memcpy._x_memcpy_u8u8 :
      arg{1} = (out, offset, in_0) /\
      arg{2} = (_out, 128, offset, _in, 32) ==> 
    forall (k : int), 0 <= k < 32 => out{1}.[(W64.to_uint offset) + k] = out{2}.[(W64.to_uint offset) + k]].
proof.
move => H0 H1 H2 H3 H4.
proc.
auto => /> *.
while(
    outlen{2} = 128 /\ inlen{2} = 32 /\
    0 <= W64.to_uint i{1} <= 32 (* 32 = inlen *) /\
    ={i, offset} /\
    list_array_eq in_0{1} H1 /\ 
    forall (k : int), 0 <= k < W64.to_uint i{1} => out{1}.[(W64.to_uint offset) + k] = out{2}.[(W64.to_uint offset) + k]
).
auto => /> * ; progress.
smt(add_1_W64).
smt.
auto => /> * ; progress.
smt(list_array_size_32).
smt.
qed.

lemma memcpy_128_64 (out : W8.t Array128.t, offset : W64.t, in_0 : W8.t Array64.t) :
    (* inlen = 64 /\ outlen = 128 *)
    (* offset + inlen <= outlen   *)
    (* offset <= outlen - inlen   *)
    let _out : W8.t list = mkseq (fun i => out.[i]) 128 in
    let _in : W8.t list = mkseq (fun i => in_0.[i]) 64 in
    let outlen = size _out in 
    let inlen = size _in in
    outlen = 128 /\ inlen = 64 /\ 0 <= W64.to_uint offset <= (outlen - inlen) =>
    equiv [M(Syscall).__memcpy_u8u8_128_64 ~ Memcpy._x_memcpy_u8u8 :
      arg{1} = (out, offset, in_0) /\
      arg{2} = (_out, 128, offset, _in, 64) ==> 
    forall (k : int), 0 <= k < 64 => out{1}.[(W64.to_uint offset) + k] = out{2}.[(W64.to_uint offset) + k]].
proof.
move => H0 H1 H2 H3 H4.
proc.
auto => /> *.
while(
    outlen{2} = 128 /\ inlen{2} = 64 /\
    0 <= W64.to_uint i{1} <= 64 (* 64 = inlen *) /\
    ={i, offset} /\
    list_array_eq_64 in_0{1} H1 /\ 
    forall (k : int), 0 <= k < W64.to_uint i{1} => out{1}.[(W64.to_uint offset) + k] = out{2}.[(W64.to_uint offset) + k]
).
auto => /> * ; progress.
smt(@W64).
smt.
auto => /> * ; progress.
smt(list_array_size_64).
smt.
qed.

lemma memcpy_96_32 (out : W8.t Array96.t, offset : W64.t, in_0 : W8.t Array32.t) :
    (* outlen = 96 /\ inlen = 32 *)
    let _out : W8.t list = mkseq (fun i => out.[i]) 96 in
    let _in : W8.t list = mkseq (fun i => in_0.[i]) 32 in
    let outlen = size _out in 
    let inlen = size _in in
    outlen = 96 /\ inlen = 32 /\ 0 <= W64.to_uint offset <= (outlen - inlen) =>
    equiv [M(Syscall).__memcpy_u8u8_96_32 ~ Memcpy._x_memcpy_u8u8 :
      arg{1} = (out, offset, in_0) /\
      arg{2} = (_out, 96, offset, _in, 32) ==> 
    forall (k : int), 0 <= k < 32 => out{1}.[(W64.to_uint offset) + k] = out{2}.[(W64.to_uint offset) + k]].
proof.
move => H0 H1 H2 H3 H4.
proc.
auto => /> *.
while (
  outlen{2} = 96 /\ inlen{2} = 32 /\
  0 <= W64.to_uint i{1} <= 32 (* 32 = inlen *) /\
  ={i, offset} /\
  list_array_eq in_0{1} H1 /\ 
  forall (k : int), 0 <= k < W64.to_uint i{1} => out{1}.[(W64.to_uint offset) + k] = out{2}.[(W64.to_uint offset) + k]
).
auto => /> * ; progress.
smt(@W64).
smt.
auto => /> * ; progress.
smt(list_array_size_32).
smt.
qed.

lemma memcpy_64_32 (out : W8.t Array64.t, offset : W64.t, in_0 : W8.t Array32.t) :
    (* outlen = 64 /\ inlen = 32 *)
    let _out : W8.t list = mkseq (fun i => out.[i]) 64 in
    let _in : W8.t list = mkseq (fun i => in_0.[i]) 32 in
    let outlen = size _out in 
    let inlen = size _in in
    outlen = 64 /\ inlen = 32 /\ 0 <= W64.to_uint offset <= (outlen - inlen) =>
    equiv [M(Syscall).__memcpy_u8u8_64_32 ~ Memcpy._x_memcpy_u8u8 :
      arg{1} = (out, offset, in_0) /\
      arg{2} = (_out, 64, offset, _in, 32) ==> 
    forall (k : int), 0 <= k < 32 => out{1}.[(W64.to_uint offset) + k] = out{2}.[(W64.to_uint offset) + k]].
proof.
move => H0 H1 H2 H3 H4.
proc.
auto => /> *.
while (
  outlen{2} = 64 /\ inlen{2} = 32 /\
  0 <= W64.to_uint i{1} <= 32 (* 32 = inlen *) /\
  ={i, offset} /\
  list_array_eq in_0{1} H1 /\ 
  forall (k : int), 0 <= k < W64.to_uint i{1} => out{1}.[(W64.to_uint offset) + k] = out{2}.[(W64.to_uint offset) + k]
).
auto => /> * ; progress.
smt(@W64).
smt.
auto => /> * ; progress.
smt(list_array_size_32).
smt.
qed.

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

(*********************************************************************************************)
(************************************** MEMSET ***********************************************)
(*********************************************************************************************)

(*
  __memset_u8_4   is always called with value = W8.of_int 255 (0xFF)
  __memset_u8_128 is always called with value = W8.of_int 0
*)

lemma memset_u8_1 (_a : W8.t Array4.t):
    equiv[M(Syscall).__memset_u8_4 ~ Memset.memset_u8 :
      arg{1} = (_a, W8.of_int 255) /\ arg{2} = (to_list _a, W64.of_int 4, W8.of_int 255) ==>
        res{2} = to_list res{1}].
proof.
proc.
auto => />.
while (
  to_uint inlen{2} = 4 /\
  ={i, value} /\
  0 <= to_uint i{2} <= to_uint inlen{2} /\
  a{2} = to_list a{1}  
) ; last by auto.
auto => />.
move => *.
do split.
smt(@W64).
smt(@W64).
smt. (* TODO: replace with smt(array_4_list_put). when it is a lemma and not an axiom*)
smt(@W64).
smt(@W64).
qed.

lemma memset_u8_2 (_a : W8.t Array128.t):
    equiv[M(Syscall).__memset_u8_128 ~ Memset.memset_u8 :
      arg{1} = (_a, W8.zero) /\ arg{2} = (to_list _a, W64.of_int 128, W8.zero) ==>
        res{2} = to_list res{1}].
proof.
proc.
auto => />.
while (
  to_uint inlen{2} = 128 /\
  ={i, value} /\
  0 <= to_uint i{2} <= to_uint inlen{2} /\
  a{2} = to_list a{1}  
) ; last by auto.
auto => />.
move => *.
do split.
smt(@W64).
smt(@W64).
smt. (* TODO: replace with smt(array_128_list_put). when it is a lemma and not an axiom*)
smt(@W64).
smt(@W64).
qed.

(*********************************************************************************************)
(************************************ MEMCPY PTR *********************************************)
(*********************************************************************************************)

lemma memcpy_p_1 (_out : W8.t Array32.t, _offset : W64.t, _in : W64.t, _inlen : W64.t) :
    equiv[M(Syscall).__memcpy_u8u8p_32 ~ Memcpy._x_memcpy_u8u8p :
      arg{1} = (_out, _offset, _in, _inlen) /\ 
      arg{2} = (to_list _out, _offset, _in, _inlen) /\
      ={Glob.mem} ==> 
         res{2}.`1 = to_list res{1}.`1 /\ res{1}.`2 = res{2}.`2].
proof.
proc.
while(
  ={i, offset, inlen, Glob.mem} /\
  0 <= to_uint i{1} <= to_uint inlen{1} /\
  out{2} = to_list out{1} /\
  in_0{1} = in_0{2} /\
  0 <= to_uint inlen{2} 
).
auto => /> *.
do split.
smt(@W64).
smt(@W64).
smt.
auto => /> *.
by smt(@W64).
qed.

lemma memcpy_p_2 (_out : W8.t Array64.t, _offset : W64.t, _in : W64.t, _inlen : W64.t) :
    equiv[M(Syscall).__memcpy_u8u8p_64 ~ Memcpy._x_memcpy_u8u8p :
      arg{1} = (_out, _offset, _in, _inlen) /\ 
      arg{2} = (to_list _out, _offset, _in, _inlen) /\
      ={Glob.mem} ==> 
         res{2}.`1 = to_list res{1}.`1 /\ res{1}.`2 = res{2}.`2].
proof.
proc.
while(
  ={i, offset, inlen, Glob.mem} /\
  0 <= to_uint i{1} <= to_uint inlen{1} /\
  out{2} = to_list out{1} /\
  in_0{1} = in_0{2} /\
  0 <= to_uint inlen{2} 
).
auto => /> *.
do split.
smt(@W64).
smt(@W64).
smt.
auto => /> *.
by smt(@W64).
qed.
