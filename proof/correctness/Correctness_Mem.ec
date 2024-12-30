pragma Goals : printall.

require import AllCore List RealExp IntDiv.

from Jasmin require import JModel.

require import Array3 Array32 Array64 Array128 Array2144.
require import Array352.

require import XMSS_IMPL.
require import Utils2 Repr2.
require import Termination.

require import Params Parameters. 

(* Copia de memoria para memoria *)
(* Apagar este lemma: isto tem que ser phoare *)
lemma __memcpy_mem_mem (mem : global_mem_t) (o_ptr i_ptr len o_off i_off : W64.t)  :
    hoare[
      M(Syscall).__memcpy_u8pu8p :
      arg = (o_ptr, o_off, i_ptr, i_off, len) /\
      valid_ptr (i_ptr + i_off) len /\
      valid_ptr (o_ptr + o_off) len /\
      0 <= to_uint len < W64.max_uint /\
      
      Glob.mem = mem
      ==>
      
      load_buf Glob.mem (o_ptr + o_off) (to_uint len) = 
      load_buf Glob.mem (i_ptr + i_off) (to_uint len) /\
      
      (* o resto da memoria fica inalterada *)
      forall (k : int), 0 <= k < W64.max_uint =>
        !(to_uint (o_ptr + o_off) <= k < to_uint (o_ptr + o_off + len)) =>
          loadW8 mem k = loadW8 Glob.mem k
    ].
proof.
proc => /=.

while (
  out_ptr = o_ptr /\
  out_offset = o_off + i /\
  in_ptr = i_ptr /\ 
  in_offset = i_off + i /\
  bytes = len /\
  valid_ptr (i_ptr + i_off) len /\
  valid_ptr (o_ptr + o_off) len /\
  0 <= to_uint len < W64.max_uint /\
  
  0 <= to_uint i <= to_uint bytes /\
  load_buf Glob.mem (o_ptr + o_off) (to_uint i) =  load_buf Glob.mem (i_ptr + i_off) (to_uint i) /\
  load_buf Glob.mem (o_ptr + o_off) (to_uint i) =  load_buf mem (i_ptr + i_off) (to_uint i) /\
  load_buf Glob.mem (i_ptr + i_off) (to_uint len) =  load_buf mem (i_ptr + i_off) (to_uint len) /\

      forall (k : int), 0 <= k < W64.max_uint =>
        !(to_uint (o_ptr + o_off) <= k < to_uint (o_ptr + o_off + i)) =>
          loadW8 mem k = loadW8 Glob.mem k

); last first.
- auto => /> H0 H1 H2 H3.
  do split. 
    + apply (eq_from_nth witness); first by rewrite !size_load_buf.
      rewrite size_load_buf /#.
    + apply (eq_from_nth witness); first by rewrite !size_load_buf.
      rewrite size_load_buf /#.
    + move => mem0 i0.
      rewrite ultE => H4 H5 H6.
      have E: to_uint i0 = to_uint len by smt().
      rewrite E => H7 H8 *.
      split => [| /#].
      by assumption.

auto => /> &hr H0 H1 H2 H3 H4 H5 H6 H7.
rewrite ultE => H8 *.

(* ============================================================================================================= *)

(* rewrite H6, H7 and H8 as a forall *)
have E6 : forall (k : int), 0 <= k < to_uint i{hr} => 
          Glob.mem{hr}.[to_uint (o_ptr + o_off) + k] =
          Glob.mem{hr}.[to_uint (i_ptr + i_off) + k].
- move => k?.
  have ->: Glob.mem{hr}.[to_uint (o_ptr + o_off) + k] = nth witness (load_buf Glob.mem{hr} (o_ptr + o_off) (to_uint i{hr})) k by rewrite nth_mkseq ///#.
  rewrite H6.
  by rewrite nth_mkseq.

have E7 : forall (k : int), 0 <= k < to_uint i{hr} => 
          Glob.mem{hr}.[to_uint (o_ptr + o_off) + k] =
          mem{hr}.[to_uint (i_ptr + i_off) + k].
- move => k?.
  have ->: Glob.mem{hr}.[to_uint (o_ptr + o_off) + k] = nth witness (load_buf Glob.mem{hr} (o_ptr + o_off) (to_uint i{hr})) k by rewrite nth_mkseq ///#.
  rewrite H7.
  by rewrite nth_mkseq.

have E8 : forall (k : int), 0 <= k < to_uint len => 
          Glob.mem{hr}.[to_uint (i_ptr + i_off) + k] =
          mem{hr}.[to_uint (i_ptr + i_off) + k].
- move => k?.
  have ->: Glob.mem{hr}.[to_uint (i_ptr + i_off) + k] = nth witness (load_buf Glob.mem{hr} (i_ptr + i_off) (to_uint len)) k by rewrite nth_load_buf.
  by rewrite H8 nth_load_buf.

(* ============================================================================================================= *)

do split; 6..8: by admit.
- ring.
- ring.
- rewrite to_uintD /#.
- rewrite to_uintD /#.
- apply (eq_from_nth witness); first by rewrite !size_load_buf // to_uintD /#.
  rewrite size_load_buf to_uintD_small 1..3:/# /= => j?.
  rewrite !nth_load_buf // /storeW8 /loadW8.
  rewrite !get_setE.
  case (j = to_uint i{hr}) => [-> | ?]; last by admit.
  admit.
qed. 


lemma p_memcpy_mem_mem (mem : global_mem_t) (o_ptr i_ptr len o_off i_off : W64.t)  :
    phoare[
      M(Syscall).__memcpy_u8pu8p :
      arg = (o_ptr, o_off, i_ptr, i_off, len) /\
      valid_ptr (i_ptr + i_off) len /\
      valid_ptr (o_ptr + o_off) len /\
      0 <= to_uint len < W64.max_uint /\
      
      Glob.mem = mem
      ==>
      
      load_buf Glob.mem (o_ptr + o_off) (to_uint len) = 
      load_buf Glob.mem (i_ptr + i_off) (to_uint len) /\
      
      (* o resto da memoria fica inalterada *)
      forall (k : int), 0 <= k < W64.max_uint =>
        !(to_uint (o_ptr + o_off) <= k < to_uint (o_ptr + o_off + len)) =>
          loadW8 mem k = loadW8 Glob.mem k
    ] = 1%r.
proof.
admit.
qed.

(* Obs: Este lema precisa de ser phoare p ser usado na prova do treehash *)     
lemma memcpy_treehash_node_2 (_stack_impl : W8.t Array352.t, o : W64.t) (stack_spec : nbytes list) :
    n = XMSS_N =>
    phoare [
      M(Syscall).__memcpy_u8u8_2_64_352 :

      size stack_spec = 11 /\ 

      sub _stack_impl 0 (XMSS_N * min (to_uint o) (size stack_spec)) = 
      sub_list (nbytes_flatten stack_spec) 0 (XMSS_N * min (to_uint o) (size stack_spec)) /\

      arg.`2 = _stack_impl /\
      arg.`3 = (o - W64.of_int 2) * (W64.of_int 32) /\
      arg.`4 = (W64.of_int 64)
      ==>
      to_list res.`1 = val (nth witness stack_spec (to_uint (o - (of_int 2)%W64)))  ++ 
                       val (nth witness stack_spec (to_uint (o - (of_int 1)%W64)))
    ] = 1%r.
proof.
rewrite /XMSS_N => n_val.
proc => /=.
conseq />.
admit. 
qed.   

lemma write_buf_ptr (mem : global_mem_t) (ptr _offset : W64.t) (buf : W8.t Array32.t) :
    hoare [
      M(Syscall).__memcpy_u8pu8_32 :
      valid_ptr_i ptr 32 /\
      arg = (ptr, _offset, buf) /\
      Glob.mem = mem
      ==>
      load_buf Glob.mem (ptr + _offset) 32 = to_list buf /\
      (* O resto da memoria continua inalterada *)
      (forall (k : address), 
        (0 <= k < W64.max_uint =>
        (!(to_uint ptr + to_uint _offset <= k < to_uint ptr + to_uint _offset + 32) =>
        loadW8 mem k = loadW8 Glob.mem k))
      ) /\
      res.`1 = ptr /\
      res.`2 = _offset + W64.of_int 32 
    ].
proof.
proc => /=.
sp.
admit.
qed.
(*

print address.
while (
  out = ptr /\
  in_0 = buf /\
  valid_ptr_i ptr 32 /\
  0 <= to_uint i <= 32 /\
  forall (k : int), 0 <= k < to_uint i => buf.[to_uint i] = 
                                          loadW8 
                                          Glob.mem
                                          (to_uint (ptr + offset))
); last by admit.      
    + auto => /> &hr H0 H1 H2 H3 H4 H5*.
      do split; 1,2: by smt(@W64 pow2_64).
      move => k??.
      rewrite /loadW8 /storeW8 get_setE.
      rewrite ifF; first by smt(@W64 pow2_64).
      admit.
qed.

lemma p_write_buf_ptr (ptr _offset : W64.t) (buf : W8.t Array32.t) :
    phoare [
      M(Syscall).__memcpy_u8pu8_32 :
      valid_ptr_i ptr 32 /\
      arg = (ptr, _offset, buf) 
      ==>
      load_buf Glob.mem ptr 32 = to_list buf
    ] = 1%r.
proof.
proc => /=.
admit.
qed.
*)
      

(* FIXME: Remove this. this lemma already exists: put_out *)
lemma put_out_of_bounds (l : W8.t list) (v : W8.t) (idx : int) :
    size l <= idx =>
    put l idx v = l.
proof.
by move => ?; rewrite /put ifF 1:/#.
qed.

lemma treehash_memcpy_ll : 
    phoare [ M(Syscall).__memcpy_u8u8_3_352_32 : arg.`4 = 32 ==> true] = 1%r.
proof. by proc; while (true) (32 - i); auto => /> /#. qed.

lemma treehash_memcpy (node : W8.t Array32.t) (stack : nbytes list) (_stack : W8.t Array352.t) (offset : W64.t) : 
    n = XMSS_N => 
    hoare [
      M(Syscall).__memcpy_u8u8_3_352_32 :
      0 <= to_uint offset /\
      size stack = 11 /\
      sub _stack 0 (XMSS_N * min (to_uint offset) (size stack)) = sub_list (nbytes_flatten stack) 0  (XMSS_N * min (to_uint offset) (size stack)) /\
      arg = (_stack, node, offset * (W64.of_int 32), 32) 
      ==> 
      sub _stack 0 (XMSS_N * min (to_uint offset) (size stack)) =
      sub_list
          (nbytes_flatten
             (put stack (to_uint offset) ((insubd (to_list node)))%NBytes)) 
          0
          (XMSS_N * min (to_uint offset + 1) (size stack))
    ].
proof.
rewrite /XMSS_N => n_val.
proc => /=.
admit.
qed.

(*
sp. 
while ( 
  bytes = 32 /\
  aux = bytes /\
  0 <= i <= 32 /\
  in_0 = node /\
  out_offset = offset * (of_int 32)%W64 /\
  0 <= to_uint offset /\
  size stack = 11 /\
  (forall (k : int), !(to_uint out_offset <= k < to_uint (out_offset + (of_int k)%W64)) => out.[k] = _stack.[k]) /\
  (forall (k : int), 0 <= k < i => out.[to_uint (out_offset + (of_int k)%W64)] = node.[k]) 
); last first.
    + auto => /> H0 H1 H2 *.
      split => [/# |].
      move => i0 out0 ???.
      have ->: i0 = 32 by smt().
      move => H3 H4.
      case (to_uint offset < size stack) => Ha.
(* ====== this is the in bounds case [of the last subgoal of while] *)
      have E: min (to_uint offset) (size stack) = to_uint offset by smt(). 
      rewrite E /=.
      rewrite H1 in Ha.
      apply (eq_from_nth witness); first by rewrite size_sub 1:/# size_sub_list /#.
      rewrite size_sub 1:/# => j?.
      rewrite -E H2.
      rewrite E /sub_list !nth_mkseq //= nth_nbytes_flatten 1:/# nth_nbytes_flatten; first by rewrite size_put H1 /#.
      rewrite nth_put 1:/#. 
      rewrite ifF /#.
(* ====== this is the out of bounds case [of the last subgoal of while] *)  
      have E: min (to_uint offset) (size stack) = size stack by smt().
      rewrite E H1 /=.
      rewrite H1 in Ha.
      apply (eq_from_nth witness); first by rewrite size_sub // size_sub_list.
      rewrite size_sub // => j?.
      rewrite nth_sub 1:/# /= /sub_list nth_mkseq 1:/# /= nth_nbytes_flatten; first by rewrite size_put /#.
      have ->: (put stack (to_uint offset) ((insubd (to_list node)))%NBytes) = stack by smt(put_out_of_bounds).
      have ->: _stack.[j] = nth witness (sub _stack 0 (32 * min (to_uint offset) (size stack))) j by rewrite E nth_sub /#.
      rewrite H2 /sub_list nth_mkseq 1:/# /= nth_nbytes_flatten /#.

(* ===== this is the first goal of while *)
auto => /> &hr H0 H1 H2 H3 H4 H5 *.
do split.
    - smt(). 
    - smt().
    - case (to_uint offset < size stack) => Ha; last by admit. 
        * move => k?.
          rewrite get_setE; first by smt(@W64 pow2_64).
          case (k = to_uint (offset * (of_int 32)%W64 + (of_int i{hr})%W64)) => Hb; last first.
             - rewrite H4 /=; smt(@W64 pow2_64).
             - admit.
    - case (to_uint offset < size stack) => Ha.
        * move => k??.
          rewrite get_setE; first by smt(@W64 pow2_64).
          case (k = i{hr}) => Hb. 
             * rewrite ifT; first by smt(@W64 pow2_64). 
               congr; smt().
             * rewrite ifF; first by smt(@W64 pow2_64).
               smt().
        * move => k??.
          search "_.[_<-_]".
          admit.
qed.
*)

lemma p_treehash_memcpy (node : W8.t Array32.t) (stack : nbytes list) (_stack : W8.t Array352.t) (offset : W64.t) : 
    n = XMSS_N => 
    phoare [
      M(Syscall).__memcpy_u8u8_3_352_32 :
      0 <= to_uint offset /\
      size stack = 11 /\
      sub _stack 0 (XMSS_N * min (to_uint offset) (size stack)) = sub_list (nbytes_flatten stack) 0  (XMSS_N * min (to_uint offset) (size stack)) /\
      arg = (_stack, node, offset * (W64.of_int 32), 32) 
      ==> 
      sub res 0 (XMSS_N * min (to_uint offset + 1) (size stack)) =
      sub_list
          (nbytes_flatten
             (put stack (to_uint offset) ((insubd (to_list node)))%NBytes)) 
          0
          (XMSS_N * min (to_uint offset + 1) (size stack))
    ] = 1%r.
proof.
admit.
qed.

lemma p_treehash_memcpy_2 (node : W8.t Array32.t) (stack : nbytes list) (_stack : W8.t Array352.t) (offset : W64.t) : 
    n = XMSS_N => 
    phoare [
      M(Syscall).__memcpy_u8u8_3_352_32 :
      0 <= to_uint offset /\
      size stack = 11 /\
      sub _stack 0 (XMSS_N * min (to_uint offset) (size stack)) = sub_list (nbytes_flatten stack) 0  (XMSS_N * min (to_uint offset) (size stack)) /\
      arg = (_stack, node, (offset - W64.of_int 2) * (W64.of_int 32), 32) 
      ==> 
      sub res 0 (n * min (to_uint offset) (size stack)) =
      sub_list
          (nbytes_flatten
             (put stack (to_uint (offset - W64.of_int 2)) ((insubd (to_list node)))%NBytes)) 
          0
          (n * min (to_uint offset) (size stack))
    ] = 1%r.
proof.
admit.
qed.

lemma _memcpy_u8u8_2_64_2144_post (_in : W8.t Array2144.t, oi : W64.t):
    hoare [
      M(Syscall).__memcpy_u8u8_2_64_2144 : 
      arg.`2 = _in /\
      arg.`3 = oi /\
      arg.`4 = W64.of_int 64 /\
      0 <= to_uint oi < W32.max_uint /\
      0 <= to_uint (oi + W64.of_int 64) < 2144
      ==>
      to_list res.`1 = sub _in (to_uint oi) 64
    ].
proof.
proc => //=.
while (  
  in_0 = _in /\ 
  bytes = (of_int 64)%W64 /\
  (0 <= to_uint oi < 2144) /\

  0 <= to_uint i <= 64 /\
  in_offset = oi + i /\

  (forall (k : int), 0 <= k < to_uint i => out.[k] = in_0.[to_uint oi + k]) 
).
    + auto => /> &hr H0 H1 H2 H3 H4 H5.  
      do split.
          * rewrite to_uintD /= #smt:(modz_small).
          * move => ?. 
            rewrite to_uintD /= #smt:(@W64 pow2_64).
          * ring.
          * move => k??.
            rewrite get_setE 1:#smt:(@W64).
            case (k = to_uint i{hr}) => H; first by rewrite H to_uintD /#.
            rewrite H4 // #smt:(@W64).
    + auto => /> &hr ????; do split.
          * smt(@W64 pow2_64). 
          * smt().  
          * move => i0 out0 ????. 
            have ->: to_uint i0 = 64 by smt(@W64 pow2_64). 
            move => H. 
            apply (eq_from_nth witness); first by rewrite size_to_list size_sub.
            rewrite size_to_list => j?.
            by rewrite get_to_list H // nth_sub.
qed.


lemma memcpy_u8u8_2_64_2144_post (_in : W8.t Array2144.t, oi : W64.t):
    phoare [
      M(Syscall).__memcpy_u8u8_2_64_2144 : 
      arg.`2 = _in /\
      arg.`3 = oi /\
      arg.`4 = W64.of_int 64 /\
      0 <= to_uint oi < W32.max_uint /\
      0 <= to_uint (oi + W64.of_int 64) < 2144
      ==>
      to_list res.`1 = sub _in (to_uint oi) 64
    ] = 1%r.
proof.
proc => /=. 
while (
  #{/~in_offset = oi}pre /\ 
  to_uint in_offset = to_uint oi + to_uint i /\  
  0 <= to_uint i <= to_uint bytes /\
  sub out 0 (to_uint i) = sub _in (to_uint oi) (to_uint i)
)
(to_uint bytes - to_uint i); last first.
  + auto => /> &hr H0 H1 H2 H3. 
    split.
      - apply (eq_from_nth witness); first by rewrite !size_sub.    
        rewrite size_sub /#.
      - move => i0 out0. 
        rewrite ultE of_uintK /=.
        move => out0_0.
        split => [/# |].
        move => H4 H5 H6 H7.
        have ->: to_uint i0 = 64 by smt().
        move => <-.
        apply (eq_from_nth witness); first by rewrite size_to_list size_sub.
        rewrite size_to_list => ??.
        by rewrite get_to_list nth_sub. 
    + auto => /> &hr.
      rewrite ultE of_uintK /= => H0 H1 H2 H3 H4 H5 H6 H7 H8. 
      do split; 2,3,5: by rewrite to_uintD /#.
          - rewrite !to_uintD_small 1,2:/# H4 /#.
          - apply (eq_from_nth witness); first by rewrite !size_sub to_uintD /#.
            rewrite size_sub to_uintD_small 1..3:/# /= => j?.
            rewrite !nth_sub //= get_setE //.
            case (j = to_uint i{hr}) => [-> /# |?]. 
            have ->: out{hr}.[j] = nth witness (sub out{hr} 0 (to_uint i{hr})) j by rewrite nth_sub /#.
            rewrite H7.
            rewrite nth_sub // /#.
qed.

(** -------------------------------------------------------------------------------------------- **)

lemma or_zero(w0 w1 : W8.t) : 
    (w0 `|` w1 = W8.zero) <=> (w0 = W8.zero /\ w1 = W8.zero).
proof.
split; last first.
  + move => [-> ->].
    by rewrite or0w.
  + rewrite !wordP => H.
    case (w0 = W8.zero).
      * move => -> /= k kb. move : (H k kb) => /= /#. 
      * move => *. have Hk : exists k, 0 <= k < 8 /\ w0.[k]. 
         - move : (W8.wordP w0 W8.zero); smt(W8.zerowE W8.get_out).
        elim Hk => k [kb kval]. move : (H k kb). by rewrite orwE kval.
qed.

lemma xor_eq (w0 w1 : W8.t) :
    w0 `^` w1 = W8.zero => w0 = w1 by smt(@W8). 
    
(** -------------------------------------------------------------------------------------------- **)

(******************************************************************************)
(******************               MEMSET                          *************)
(******************************************************************************)

lemma memset_4_post (input : W8.t Array3.t, v : W8.t) :
    hoare [M(Syscall).__memset_u8_3 : arg=(input, v) ==> 
     (forall (k : int), 0 <= k < 3 => (res.[k] = v))].
proof.
proc.
while (
  0 <= to_uint i <= 3 /\ 
  value = v /\
  (forall (k : int), 0 <= k < to_uint i => (a.[k] = value))
); auto => /> *.
- do split; 1,2: by smt(@W64). 
  move => ???. 
  rewrite get_setE #smt:(@W64).
- split => [/# |]. 
  move => ?i0???.   
  (have ->: to_uint i0 = 3 by smt(@W64 pow2_64)) => /#. 
qed.

lemma p_memset_4_post (input : W8.t Array3.t, v : W8.t) :
    phoare [M(Syscall).__memset_u8_3 : arg=(input, v) ==> 
     (forall (k : int), 0 <= k < 3 => (res.[k] = v))] = 1%r.
proof.
by conseq memset_4_ll (memset_4_post input v); auto => />.
qed.

lemma memset_128_post (input : W8.t Array128.t, v : W8.t) :
    hoare [M(Syscall).__memset_u8_128 : arg=(input, v) ==> 
     (forall (k : int), 0 <= k < 128 => (res.[k] = v))].
proof.
proc.
while (
  0 <= to_uint i <= 128 /\ 
  value = v /\
  (forall (k : int), 0 <= k < to_uint i => (a.[k] = value))
); auto => /> *.
- do split ; 1,2: by smt(@W64). 
  move => ???. 
  rewrite get_setE #smt:(@W64).
- split => [/# |]. 
  move => ?i0???.   
  (have ->: to_uint i0 = 128 by smt(@W64 pow2_64)) => /#.
qed.

lemma p_memset_128_post (input : W8.t Array128.t, v : W8.t) :
    phoare [M(Syscall).__memset_u8_128 : arg=(input, v) ==> 
     (forall (k : int), 0 <= k < 128 => (res.[k] = v))] = 1%r.
proof.
conseq memset_128_ll (memset_128_post input v); auto => />.
qed.

lemma memset_zero_post :
    hoare [M(Syscall).__memset_zero_u8 : true ==> forall (k : int), 0 <= k < 3 => (res.[k] = W8.zero)].
proof.
proc.
while (
  0 <= to_uint i <= 3 /\   
  (forall (k : int), 0 <= k < to_uint i => (a.[k] = W8.zero))
); auto => /> *.
- do split ; 1,2: by smt(@W64).  
  move => ???.
  rewrite get_setE #smt:(@W64).
- split => [/# |]. 
  move => ?i0???.   
  (have ->: to_uint i0 = 3 by smt(@W64 pow2_64)) => /#. 
qed.

lemma p_memset_zero_post :
    phoare[M(Syscall).__memset_zero_u8 : true ==> 
      forall (k : int), 0 <= k < 3 => (res.[k] = W8.zero)] = 1%r.
proof.
conseq memset_zero_ll memset_zero_post.
auto => />.
qed.

lemma _memset_nseq : 
    hoare [
      M(Syscall).__memset_zero_u8 :
      true
      ==>
      to_list res = nseq 3 W8.zero
    ].
proof.
proc.
while (
  0 <= to_uint i <= 3 /\
  forall (k : int), 0 <= k < to_uint i => a.[k] = W8.zero
). 
    + auto => /> *.
      do split; 1,2:smt(@W64).
      move => ???. 
      rewrite get_setE #smt:(@W64).
    + auto => /> &hr ; split => [/# |]. 
      move => ? i???. 
      have ->: to_uint i = 3 by smt(@W64 pow2_64).
      move => ?. 
      apply (eq_from_nth witness); [ rewrite size_to_list size_nseq //= |].
      rewrite size_to_list => *. 
      rewrite nth_nseq 1:/# get_to_list /#.
qed.

lemma memset_nseq : 
    phoare [ M(Syscall).__memset_zero_u8 : true ==>
       to_list res = nseq 3 W8.zero] = 1%r
          by conseq memset_zero_ll _memset_nseq; auto.

lemma memset_ptr_post (ptr : W64.t, len : W64.t, v : W8.t) :
    hoare [M(Syscall).__memset_u8_ptr : 
      0 <= to_uint len < W64.modulus /\
      0 <= to_uint ptr /\ to_uint ptr + to_uint len < W64.modulus /\ 
      arg=(ptr, len, v) ==>
        forall (k:int), 0 <= k < to_uint len => (loadW8 Glob.mem (W64.to_uint (ptr  + (W64.of_int k)))) = v].
proof.
proc => /=.
while (
  #pre /\
  0 <= to_uint i <= to_uint inlen /\
  (forall (k : int), 0 <= k < to_uint i => loadW8 Glob.mem ((W64.to_uint _ptr) + k) = v )
); last first.
    + auto => /> &hr H0 H1 H2 H3.
      split => [/# |].
      move => mem j.
      rewrite ultE => H4 H5 H6.
      have ->: j = len by smt(@W64 pow2_64).
      move => H7 k??.
      rewrite /loadW8 to_uintD_small of_uintK /#. 
    + auto => /> &hr H0 H1 H2 H3 H4 H5 H6.
      rewrite ultE => H7.
      do split.
         - rewrite to_uintD /#.
         - rewrite to_uintD /#.
         - rewrite to_uintD_small 1:/# => k??.
           rewrite /loadW8 /storeW8 get_setE. 
           case (k = to_uint i{hr}) => [-> |?].
              + rewrite ifT // to_uintD /#.
              + rewrite ifF; [rewrite to_uintD /# |].
                rewrite /loadW8 in H6.
                apply H6.
                smt(@W64 pow2_64).
qed.

(******************************************************************************)
(******************               MEMCPY                          *************)
(******************************************************************************)

lemma memcpy_ptr_correct (ptr : W64.t):
    hoare [M(Syscall)._x_memcpy_u8u8p : 
      arg.`2 = ptr /\  
      0 <= (to_uint ptr) + 32 <= W64.modulus /\
      0 <= to_uint ptr ==>
        res = Array32.init (fun (i : int) => loadW8 Glob.mem (to_uint ptr + i))].
proof.
proc.
inline * ; wp ; sp.
while (
  in_ptr1  = ptr /\
  0 <= (to_uint ptr) + 32 <= W64.modulus /\
  0 <= to_uint ptr /\
  
  0 <= i <= 32 /\
  0 <= to_uint in_ptr{hr} + 32 <= W64.modulus /\
  forall (k : int), 0 <= k < i => (out1.[k] = loadW8 Glob.mem ((to_uint ptr) + k))
).
    + auto => /> &hr H0 H1 H2 H3 H4 H5 H6 H7 H8C.
      do split; 1,2:smt().
      move => k??.
      rewrite get_setE //=.
      case (k = i{hr}) => E.
          * congr; rewrite E #smt:(@W64 pow2_64).
          * apply H7 => /#.      
    + auto => /> &hr H0 H1 H2. 
      split => [/# | i0 out0 ???]. 
      have ->: i0 = 32 by smt().
      move => H3.
      rewrite tP => j?.
      rewrite initiE //=. 
      by apply H3.
qed.

lemma memcpy_ptr_ll :
    phoare [
      M(Syscall)._x_memcpy_u8u8p : 
      0 <= (to_uint arg.`2) + 32 <= W64.modulus /\
      0 <= to_uint arg.`2 
      ==>
      true
    ] = 1%r.
proof.
proc.
inline; wp; sp.
while (true) (32 - i); auto => /> /#. 
qed.

lemma p_memcpy_ptr_correct (ptr : W64.t):
    phoare [M(Syscall)._x_memcpy_u8u8p : 
      arg.`2 = ptr /\  
      0 <= (to_uint ptr) + 32 <= W64.modulus /\
      0 <= to_uint ptr ==>
        res = Array32.init (fun (i : int) => loadW8 Glob.mem (to_uint ptr + i))] = 1%r.
proof.
by conseq memcpy_ptr_ll (memcpy_ptr_correct ptr).
qed.

lemma _x_memcpy_u8u8_p (x : W8.t Array32.t) :
hoare [M(Syscall)._x_memcpy_u8u8_32_32 : arg.`2 = x ==> res = x].
proof.
proc.
inline.
wp; sp.
while (
  0 <= to_uint i <= 32 /\ 
  (forall (k : int), 0 <= k < to_uint i => (out1.[k] = in_01.[k])) /\

  in_01 = x
).
    + auto => /> &hr H0 H1 H2 H3. 
      do split; 1,2: by smt(@W64).
      move => k??.
      rewrite get_setE 1:#smt:(@W64).
      case (k = to_uint i{hr}) => [/# | *].
      apply H2.
      smt(@W64).
    + skip => /> &hr.
      split => [/# | i0 out10 ???].
      have ->: to_uint i0 = 32 by smt(@W64 pow2_64).
      by rewrite tP.
qed.


lemma _x_memcpy_u8u8_post (x : W8.t Array32.t) :
    phoare [
        M(Syscall)._x_memcpy_u8u8_32_32 : 
          arg.`2 = x ==> res = x] = 1%r
            by conseq _x_memcpy_u8u8_32_32_ll (_x_memcpy_u8u8_p x).

lemma _x_memcpy_u8u8_64_ (x : W8.t Array64.t) :
    hoare [M(Syscall)._x_memcpy_u8u8_64_64 : arg.`2 = x ==> res = x].
proof.
proc. 
inline; wp; sp. 
while (
  in_01 = x /\
  0 <= to_uint i <= 64 /\
  (forall (k : int), 0 <= k < to_uint i => (out1.[k] = x.[k]))
).
    + auto => /> &hr H0 H1 H2 H3.
      do split; 1,2: by smt(@W64). 
      move => k??. 
      rewrite get_setE 1:#smt:(@W64).
      case (k = to_uint i{hr}) => [/# | *].
      apply H2.
      smt(@W64).
    + auto => /> &hr.
      split => [/# | i0 out10 ???].
      have ->: to_uint i0 = 64 by smt(@W64 pow2_64).
      by rewrite tP.
qed.


lemma _x_memcpy_u8u8_64_post (x : W8.t Array64.t) :
    phoare [M(Syscall)._x_memcpy_u8u8_64_64 : arg.`2 = x ==> res = x] = 1%r
      by conseq _x_memcpy_u8u8_64_64_ll (_x_memcpy_u8u8_64_ x).


(******************************************************************************)
(******************               MEMCMP                          *************)
(******************************************************************************)

lemma memcmp_true (x y : W8.t Array32.t) :
        hoare[M(Syscall).__memcmp : x = y /\ arg = (x, y) ==> res = W8.zero].
proof.
proc.
while(0 <= to_uint i <= 32 /\ a = b /\ acc = W8.zero) ; auto => /> *; smt(@W64).
qed.


(* conseq is not working here so i wrote the proof twice *)
lemma p_memcmp_true (x y : W8.t Array32.t) :
        phoare[M(Syscall).__memcmp : x = y /\ arg = (x, y) ==> res = W8.zero] = 1%r.
proof.
proc.
while(0 <= to_uint i <= 32 /\ a = b /\ acc = W8.zero) (32 - to_uint i); auto => /> *; smt(@W64).
qed.


lemma memcmp_false (x y : W8.t Array32.t) :
        hoare[M(Syscall).__memcmp : x<>y /\ arg = (x, y) ==> res <> W8.zero].
proof.
have E : exists (i : int), 0 <= i < 32 => x.[i] <> y.[i] by smt(@Array32). 
proc.
while (
  #pre /\
  (exists (i : int), 0 <= i && i < 32 => x.[i] <> y.[i]) /\
  0 <= to_uint i <= 32 /\ 
  (acc = W8.zero <=> forall (k : int), 0 <= k < to_uint i => x.[k] = y.[k])
). 
    + auto => /> &hr i0????H0. 
      rewrite ultE of_uintK (: 32 %% W64.modulus = 32) 1:/# => ?. 
      do split; 1,2: smt(@W64).       
         * move => ?. 
           have E1 : acc{hr} = W8.zero by smt(or_zero). 
           have E2 : x.[to_uint i{hr}] `^` y.[to_uint i{hr}] = W8.zero by smt(or_zero).
           have E3 : x.[to_uint i{hr}] = y.[to_uint i{hr}] by smt(xor_eq).
           have E4 : forall (k : int), 0 <= k && k < to_uint i{hr} => x.[k] = y.[k] by smt(). 
           rewrite to_uintD_small /#.
         * rewrite to_uintD_small 1:/# (: to_uint W64.one = 1) 1:/# => H.
           rewrite or_zero; split; [rewrite H0 | rewrite H ] => /#.
    + auto => /> *; split => [/# | ?i0]. 
      rewrite ultE -lezNgt of_uintK //= => [????? ->].
      have ->: to_uint i0 = 32 by smt(). 
      smt(@Array32). 
qed.

lemma p_memcmp_false (x y : W8.t Array32.t) :
        phoare[M(Syscall).__memcmp : x<>y /\ arg = (x, y) ==> res <> W8.zero] = 1%r.
proof.
have E : exists (i : int), 0 <= i < 32 => x.[i] <> y.[i] by smt(@Array32). 
proc.
while (
  #pre /\
  (exists (i : int), 0 <= i && i < 32 => x.[i] <> y.[i]) /\
  0 <= to_uint i <= 32 /\ 
  (acc = W8.zero <=> forall (k : int), 0 <= k < to_uint i => x.[k] = y.[k])
)
(32 - to_uint i). 
    + auto => /> &hr i0????H0. 
      rewrite ultE of_uintK (: 32 %% W64.modulus = 32) 1:/# => ?. 
      do split; 1,2: smt(@W64).       
         * move => ?. 
           have E1 : acc{hr} = W8.zero by smt(or_zero). 
           have E2 : x.[to_uint i{hr}] `^` y.[to_uint i{hr}] = W8.zero by smt(or_zero).
           have E3 : x.[to_uint i{hr}] = y.[to_uint i{hr}] by smt(xor_eq).
           have E4 : forall (k : int), 0 <= k && k < to_uint i{hr} => x.[k] = y.[k] by smt(). 
           rewrite to_uintD_small /#.
         * rewrite to_uintD_small 1:/# (: to_uint W64.one = 1) 1:/# => H.
           rewrite or_zero; split; [rewrite H0 | rewrite H ] => /#.
         * smt(@W64 pow2_64).
    + auto => /> *; split => [/# | ?i0]. 
      rewrite ultE -lezNgt of_uintK //=; split => [|????? ->]; first by smt(@W64 pow2_64).
      have ->: to_uint i0 = 32 by smt(). 
      smt(@Array32). 
qed.

lemma memcpy_offset_1 (_offset_ : W64.t, _in_ : W8.t Array32.t) :
    phoare [
      M(Syscall).__memcpy_u8u8_offset : 
      arg.`2=_offset_ /\ 
      arg.`3=_in_ /\  
      0 <= to_uint _offset_ < (2144 - 32)
      ==>
      (forall (k : int), 0 <= k < 32 => (res.[to_uint _offset_ + k] = _in_.[k]))
    ] = 1%r.
proof.

conseq (: _ ==> sub res (to_uint _offset_) 32 = sub _in_ 0 32).
  + auto => /> &hr H0 H1 result.
    split => H.
        * apply (eq_from_nth witness); rewrite !size_sub // => j?.
          rewrite !nth_sub // /#.
        * move => k??.
          have ->: in_0{hr}.[k] = nth witness (sub in_0{hr} 0 32) k by rewrite nth_sub.
          by rewrite -H nth_sub.

proc => /=.

while (
  #{/~offset = _offset_}pre /\
  0 <= to_uint i <= 32 /\
  offset = _offset_ + i /\
  sub out (to_uint _offset_) (to_uint i) = sub _in_ 0 (to_uint i)  
)
(32 - to_uint i); last first.
    + auto => /> &hr H0 H1. 
      do split.
         - apply (eq_from_nth witness); first by rewrite !size_sub.
           rewrite size_sub // /#.
         - move => i0 out0.
           split; rewrite ultE of_uintK /= => H2 H3 H4; first by smt().
           have ->: to_uint i0 = 32 by smt().
           by move => ->.
    + auto => /> &hr H0 H1 H2 H3 H4.
      rewrite ultE of_uintK /= => H5.
      do split. 
          - rewrite to_uintD /#.
          - rewrite to_uintD /#.
          - by ring.
          - apply (eq_from_nth witness); first by rewrite !size_sub to_uintD /#.
            rewrite size_sub to_uintD 1:/# /= => j?.
            rewrite !nth_sub //= get_setE //; [rewrite to_uintD /# |].
            case (j = to_uint i{hr}) => [-> |?].
                - by rewrite ifT // to_uintD /#.
                - rewrite ifF; first rewrite to_uintD /#.
                  have ->: _in_.[j] = nth witness (sub _in_ 0 (to_uint i{hr})) j by rewrite nth_sub // /#. 
                  rewrite -H4 nth_sub /#.
          - rewrite to_uintD /#.
qed.

lemma _x_memcpy_u8u8_64_32_p (o : W8.t Array64.t) (x : W8.t Array32.t) :
  hoare [M(Syscall)._x_memcpy_u8u8_64_32 :
    arg.`1 = o /\
    arg.`2 = x 
    ==> 
    to_list res = (to_list x) ++ sub o 32 32
  ].
proof.
proc => /=.
inline.
wp; sp 6.
while (
  #{/~ out1 = out0}pre /\
  0 <= to_uint i <= 32 /\
  sub out1 0 (to_uint i)  = sub x 0 (to_uint i) /\
  sub out1 (to_uint i) (64 - to_uint i) = sub o (to_uint i) (64 - to_uint i)
); last first.
    + auto => />. 
      split.
        -  apply (eq_from_nth witness); first by rewrite !size_sub.
           rewrite size_sub // /#.
        - move => j outj.
          rewrite ultE of_uintK /= => H0 H1 H2 H3 H4.
          apply (eq_from_nth witness); first by rewrite size_cat !size_to_list size_sub.
          rewrite size_to_list => ii ?.
          case (0 <= ii < 32) => H. 
            + rewrite nth_cat size_to_list ifT 1:/# get_to_list.
              have ->: outj.[ii] = nth witness (sub outj 0 (to_uint j)) ii by rewrite nth_sub /#.
              by rewrite H3 nth_sub 1:/# get_to_list.
          rewrite nth_cat size_to_list ifF 1:/# get_to_list nth_sub 1:/# /=.
          have ->: o.[ii] = nth witness (sub o (to_uint j) (64 - to_uint j)) (ii - to_uint j) by rewrite nth_sub /#.
          rewrite -H4 nth_sub /#.
    + auto => /> &hr H0 H1 H2 H3.
      rewrite ultE of_uintK /= => H4.
      do split.
        - rewrite to_uintD /#.
        - rewrite to_uintD /#.
        - apply (eq_from_nth witness); [rewrite !size_sub; 1..3: by rewrite to_uintD /# |].
          rewrite size_sub; [rewrite to_uintD /#|].
          have ->: to_uint (i{hr} + W64.one) = to_uint i{hr} + 1 by rewrite to_uintD /#.
          move => j?.
          rewrite !nth_sub //= get_setE 1:/#.
          case (j = to_uint i{hr}) => [-> // | // ?]. (* Obs: move => -> // solves the first subgoal, thats why we only have one subgoal after case *)
          have ->: x.[j] = nth witness (sub x 0 (to_uint i{hr})) j by rewrite nth_sub // /#.
          rewrite -H2 nth_sub /#.
        - apply (eq_from_nth witness); first by rewrite !size_sub to_uintD /#.
          rewrite size_sub; [rewrite to_uintD /# |].
          have ->: to_uint (i{hr} + W64.one) = to_uint i{hr} + 1 by rewrite to_uintD /#.
          move => j?.
          rewrite !nth_sub // get_setE 1:/# ifF 1:/#. 
          have ->: o.[to_uint i{hr} + 1 + j] = nth witness (sub o (to_uint i{hr}) (64 - to_uint i{hr}))  (1 + j) by rewrite nth_sub /#.
          rewrite -H3 nth_sub /#.
qed.

lemma _x_memcpy_u8u8_64_32_post (o : W8.t Array64.t) (x : W8.t Array32.t) :
  phoare [M(Syscall)._x_memcpy_u8u8_64_32 :
    arg.`1 = o /\
    arg.`2 = x 
    ==> 
    to_list res = (to_list x) ++ sub o 32 32
  ] = 1%r by  conseq _x_memcpy_u8u8_64_32_ll (_x_memcpy_u8u8_64_32_p o x).

(** ----------------- nbytes copy ------------------ **)

lemma nbytes_copy_64_32 (o : W8.t Array64.t, _in : W8.t Array32.t)  : 
    hoare[
      M(Syscall).__nbytes_copy_offset_64_32 :
      arg = (o, W64.zero, _in, W64.zero) 
      ==> 
      sub res 0  32 = to_list _in /\
      sub res 32 32 = sub o 32 32 
    ].
proof.
proc => /=.
while (
  #{/~out = o}pre /\
  0 <= i <= 32 /\
  (forall (k : int), 0 <= k < i => out.[to_uint offset_out + k] = in_0.[to_uint offset_in + k]) /\
  (forall (k : int), 0 <= k < 32 => out.[32 + k] = o.[32 + k])
); last first.
    + auto => /> *.
      split => [/# | i????].
      have ->: i = 32 by smt(). 
      move => H0 H1.
      split.
         * apply (eq_from_nth witness); first by rewrite size_to_list size_sub.
           rewrite size_sub // => j?.
           by rewrite nth_sub // get_to_list H0.
         * apply (eq_from_nth witness); first by rewrite !size_sub.
           rewrite size_sub // => j?.
           by rewrite !nth_sub // H1.
auto => /> &hr ?? H0 H1 ?.
split => [/# |].
split => k??.
    + rewrite get_setE 1:#smt:(@W64 pow2_64).
      case (i{hr} = k) => H2; last first.
         * rewrite ifF; [ rewrite of_uintK |] => /#.
         * rewrite ifT; first by rewrite of_uintK /#.
           rewrite of_uintK H2 /#.
    + rewrite get_setE 1:#smt:(@W64 pow2_64).
      rewrite ifF; first by rewrite of_uintK /= /#.
      by apply H1.   
qed.

      
lemma nbytes_copy_64_32_ll : islossless M(Syscall).__nbytes_copy_offset_64_32
    by proc; while (true) (32 - i); auto => /> /#.

lemma nbytes_copy_64_32_p (o : W8.t Array64.t, _in : W8.t Array32.t)  : 
    phoare[
      M(Syscall).__nbytes_copy_offset_64_32 :
      arg = (o, W64.zero, _in, W64.zero) 
      ==> 
      sub res 0  32 = to_list _in /\
      sub res 32 32 = sub o 32 32 
    ] = 1%r
        by conseq nbytes_copy_64_32_ll (nbytes_copy_64_32 o _in).

(* ================================================================================= *)

require import Array131.

lemma nbytes_copy_131_32 (o : W8.t Array131.t, _in : W8.t Array32.t)  : 
    hoare[
      M(Syscall).__nbytes_copy_offset_131_32 :
      arg = (o, (W64.of_int 67), _in, W64.zero) 
      ==> 
      sub res 67 32 = to_list _in /\
      sub res 0 67 = sub o 0 67 /\ 
      sub res 99 32 = sub o 99 32 
    ].
proof.
proc => /=.
while (
  #{/~out = o}pre /\
  0 <= i <= 32 /\
  (forall (k : int), 0 <= k < i => out.[67 + k] = in_0.[k]) /\
  sub out 0 67 = sub o 0 67 /\ 
  sub out 99 32 = sub o 99 32 
); last first.
    + auto => />; split => [/# | i out???].
      rewrite (: i = 32) 1:/# => H0 H1 H2.
      apply (eq_from_nth witness); first by rewrite size_to_list size_sub.
      rewrite size_sub // => j?.
      rewrite nth_sub // H0 // get_to_list.

auto => /> &hr ??? H0  H1*; split => [/# |].
do split.
    + move => k??.
      rewrite get_setE; [rewrite of_uintK /# |].
      case (k = i{hr}) => [-> | ?].
          * rewrite ifT; rewrite of_uintK /#.
          * rewrite ifF; [rewrite of_uintK /# | smt()]. 
    + apply (eq_from_nth witness); first by rewrite !size_sub.
      rewrite size_sub // => j?.
      rewrite nth_sub //.
      rewrite get_setE; [rewrite of_uintK /# |].
      rewrite ifF; [rewrite of_uintK /# |].
      have ->: out{hr}.[0 + j] = nth witness (sub out{hr} 0 67) j by rewrite nth_sub.
      congr; apply H0.     
    + apply (eq_from_nth witness); first by rewrite !size_sub.
      rewrite size_sub // => j?.
      rewrite nth_sub //.
      rewrite get_setE; [rewrite of_uintK /# |].
      rewrite ifF; [rewrite of_uintK /# |].
      have ->: out{hr}.[99 + j] = nth witness (sub out{hr} 99 32) j by rewrite nth_sub.
      congr; apply H1.
qed.
      
lemma nbytes_copy_131_32_ll : islossless M(Syscall).__nbytes_copy_offset_131_32
    by proc; while (true) (32 - i); auto => /> /#.

lemma nbytes_copy_131_32_p (o : W8.t Array131.t, _in : W8.t Array32.t)  : 
    phoare[
      M(Syscall).__nbytes_copy_offset_131_32 :
      arg = (o, W64.of_int 67, _in, W64.zero) 
      ==> 
      sub res 67 32 = to_list _in /\
      sub res 0 67 = sub o 0 67 /\ 
      sub res 99 32 = sub o 99 32 
    ] = 1%r
        by conseq nbytes_copy_131_32_ll (nbytes_copy_131_32 o _in).
 
 (* ================================================================================= *)

lemma memcpy_u8u8_2_64_352_post (o : W8.t Array64.t) (_in : W8.t Array352.t) (off : W64.t):
    phoare [
       M(Syscall).__memcpy_u8u8_2_64_352 :
       arg = (o, _in, off, W64.of_int 64) /\
       0 <= to_uint off < 353 - 64      
       ==>
       to_list res.`1 = sub _in (to_uint off) 64
       ] = 1%r.
proof.
proc => /=.
conseq (: _ ==>
  forall (k : int), 0 <= k < 64 => out.[k] = _in.[to_uint off + k]
).
- auto => /> ?? out0; split => [H k?? | H].
    + have ->: out0.[k] = nth witness (to_list out0) k by rewrite get_to_list.
      by rewrite H nth_sub.
    + apply (eq_from_nth witness); first by rewrite size_to_list size_sub.  
      rewrite size_to_list => j?.
      by rewrite get_to_list H // nth_sub.

while (
  in_0 = _in /\ 
  in_offset = off + i /\
  bytes = (of_int 64)%W64 /\
  0 <= to_uint i <= 64 /\
  0 <= to_uint off < 289 /\
  forall (k : int), 0 <= k && k < to_uint i => out.[k] = _in.[to_uint off + k]
)
(64 - to_uint i); last first.     

- auto => /> ??.
  split => [/# |].
  move => i0 out0.
  split; by rewrite ultE /#.

- auto => /> &hr H0 H1 H2 H3 H4.
  rewrite ultE to_uintD_small 1:/# of_uintK /= => H5.
  do split; 2,3,5: by smt().
  * ring.
  * move => k??.
    rewrite get_setE 1:/#.
    case (k = to_uint i{hr}) => [-> | /#].
    by congr; rewrite to_uintD_small //#.
qed.

