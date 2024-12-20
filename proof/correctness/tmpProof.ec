pragma Goals : printall.

require import AllCore List RealExp IntDiv.

from Jasmin require import JModel.

require import Array3 Array32 Array64 Array128 Array2144.
require import Array352.

require import XMSS_IMPL.
require import Utils2 Repr2.
require import Termination.

require import Params Parameters. 

require import BitEncoding.
(*---*) import BitChunking.

require import StdBigop. 
(*---*) import Bigint.

lemma __memcpy_mem_mem mem (o_ptr i_ptr len o_off i_off : W64.t)  :
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
  #{/~out_offset = o_off}{/~in_offset = i_off}{/~Glob.mem = mem}pre /\
 
  0 <= to_uint i <= to_uint len /\

  load_buf Glob.mem (o_ptr + o_off) (to_uint i) =
  load_buf Glob.mem (i_ptr + i_off) (to_uint i) /\ 

  in_offset = i_off + i /\
  out_offset = o_off + i /\

  forall (k : int), 0 <= k < W64.max_uint =>
    !(to_uint (o_ptr + o_off) <= k < to_uint (o_ptr + o_off + i)) =>         loadW8 mem k = loadW8 Glob.mem k
); last first.
- auto => /> H0 H1 H2 H3. 
  split.
  + apply (eq_from_nth witness); first by rewrite !size_load_buf.
    rewrite size_load_buf // /#.
  + move => mem0 j.
    rewrite ultE => ???.
    have E: to_uint j = to_uint len by smt(). 
    rewrite E => H4 H5.
    split; first by assumption.
    smt(). 

- auto => /> &hr H0 H1 H2 H3 H4 H5 H6 H7.
  rewrite ultE => H8.
  do split.
  + rewrite to_uintD /#.
  + rewrite to_uintD /#.
  + apply (eq_from_nth witness); first by rewrite !size_load_buf // to_uintD /#.
    rewrite size_load_buf to_uintD_small 1..3:/# /= => j?.
    rewrite !nth_load_buf // /loadW8 /storeW8 get_setE.
    admit.
  + ring.
  + ring.
  + move => k?? H.
    admit.
qed.


lemma memcpy_treehash_node_2 (_stack_impl : W8.t Array352.t, o : W64.t) (stack_spec : nbytes list) :
    n = XMSS_N =>
    hoare [
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
    ].
proof.
rewrite /XMSS_N => n_val.
proc => /=.
sp.
while (
  #{/~in_offset = (o - (of_int 2)%W64) * (of_int 32)%W64}{/~ i = W64.zero}pre /\

  in_offset = (o - (of_int 2)%W64) * (of_int 32)%W64 + i /\

  0 <= to_uint i <= 64 /\

  sub out 0 (to_uint i) = sub in_0 (to_uint ((o - (of_int 2)%W64) * (of_int 32)%W64))
                                   (to_uint i)
); last first.
- auto => /> &hr H0 H1.
  have E0: val (nth witness stack_spec (to_uint (o - (of_int 2)%W64))) ++ 
           val (nth witness stack_spec (to_uint (o - W64.one))) = 
           sub_list (nbytes_flatten stack_spec) (32 * (to_uint (o - (of_int 2)%W64))) 64.
  + apply (eq_from_nth witness); first by rewrite size_cat !valP n_val size_sub_list.
    rewrite size_cat !valP n_val /= => j?.
    rewrite /sub_list nth_mkseq //= nth_nbytes_flatten. admit.
    case (0 <= j < 32) => [Hfst | Hsnd];
        rewrite nth_cat valP n_val; [by rewrite ifT 1:/#; do congr; smt(@W64 pow2_64) | rewrite ifF 1:/#].
    admit.
           
  split.
  + apply (eq_from_nth witness); first by rewrite !size_sub.
    rewrite size_sub // /#.
  + move => j out0.
    rewrite ultE of_uintK /= => H2 H3 H4.
    have ->: to_uint j = 64 by smt().
    have ->: sub out0 0 64 = to_list out0.
      * apply (eq_from_nth witness); first by rewrite size_to_list size_sub.
        by rewrite size_sub // => ??; rewrite get_to_list nth_sub.
    move => ->.
    apply (eq_from_nth witness); first by rewrite size_cat !valP n_val size_sub.
    rewrite size_sub // => i?.
    rewrite nth_sub //.
    case (0 <= to_uint o < size stack_spec) => [H_o_inbounds | H_o_out_of_bounds]; last by admit.
      * have E: min (to_uint o) (size stack_spec) = to_uint o by smt(). 
        move: H1; rewrite E => H1.
        rewrite E0.

admit.

- auto => /> &hr H0 H1 H2 H3 H4.
  rewrite ultE of_uintK /= => H5.
  do split.
  + ring.
  + rewrite to_uintD /#.
  + rewrite to_uintD /#.
  + apply (eq_from_nth witness); first by rewrite !size_sub; 1,2: by rewrite to_uintD /#.
    rewrite size_sub; first by rewrite to_uintD /#.
    rewrite to_uintD_small 1:/# /= => j?.
    rewrite !nth_sub //= get_setE 1:/#.
    case (0 <= to_uint ((o - (of_int 2)%W64) * (of_int 32)%W64 + i{hr}) < 11 * 32) 
        => /= [H_in_bounds | H_out_of_bounds]; last first.
    (* case out of bounds *)  
    case (j = to_uint i{hr}) => [-> | ?]; first by rewrite !get_out 1:/# //; smt(@W64 pow2_64).
    have ->: out{hr}.[j] = nth witness (sub out{hr} 0 (to_uint i{hr})) j by rewrite nth_sub /#. 
    by rewrite H4 nth_sub 1:/#.
    (* case in bounds *)  
    case (j = to_uint i{hr}) => [-> | ?]; last first.
      * have ->: out{hr}.[j] = nth witness (sub out{hr} 0 (to_uint i{hr})) j by rewrite nth_sub /#.       
        by rewrite H4 nth_sub 1:/#.
      * congr.
        rewrite to_uintD_small //=.
        rewrite to_uintM of_uintK /=.
        rewrite to_uintB. 
           - rewrite uleE of_uintK /=; admit.
        rewrite of_uintK.
        admit.
qed.
 




















                             
lemma p_treehash_memcpy_2 (node : W8.t Array32.t) (stack : nbytes list) 
                          (_stack : W8.t Array352.t) (_offset_ : W64.t) : 
    n = XMSS_N =>
    hoare [
      M(Syscall).__memcpy_u8u8_3_352_32 :
      0 <= to_uint _offset_ /\
      size stack = 11 /\
      sub _stack 0 (n * min (to_uint _offset_) (size stack)) = 
      sub_list (nbytes_flatten stack) 0 (n * min (to_uint _offset_) (size stack)) /\

      arg = (_stack, node, (_offset_ - W64.of_int 2) * (W64.of_int 32), 32) 

      ==>
 
      sub res 0 (n * min (to_uint _offset_) (size stack)) =
      sub_list
          (nbytes_flatten
             (put stack (to_uint (_offset_ - W64.of_int 2)) ((insubd (to_list node)))%NBytes)) 
          0
          (n * min (to_uint _offset_) (size stack))
    ].

proof.
rewrite /XMSS_N => n_val.
proc => /=.

while (
  #{/~out = _stack}pre /\
  0 <= i <= 32 /\
  sub out (to_uint( (_offset_ - (of_int 2)%W64) * (of_int 32)%W64)) i = sub in_0 0 i /\
  
forall (k : int), 0 <= k < n * size stack =>
      !(to_uint( (_offset_ - (of_int 2)%W64) * (of_int 32)%W64) <= 
        k <
       to_uint( (_offset_ - (of_int 2)%W64) * (of_int 32)%W64) + n) => 
  out.[k] = _stack.[k]
); first by admit.

- auto => /> H0 H1 H2.
  split; first by apply (eq_from_nth witness); rewrite !size_sub // /#.
  move => j out0 ???.
  have ->: j = 32 by smt().
  move => H3. 
  have E3: forall (k : int), 0 <= k < 32 => out0.[to_uint ((_offset_ - (of_int 2)%W64) * (of_int 32)%W64) + k] = node.[k].
    + move => k?. 
      have ->: node.[k] = nth witness (sub node 0 32) k by rewrite nth_sub.
      by rewrite -H3 nth_sub.
  move => H4.

  apply (eq_from_nth witness).
    + rewrite size_sub 1:/# size_sub_list // /#.
  rewrite size_sub 1:/# n_val.
  case (0 <= to_uint _offset_ < size stack) => [H_offset_in_bounds | H_offset_out_of_bounds]; last by admit.
    + have E0: min (to_uint _offset_) (size stack) = to_uint _offset_ by smt().
      rewrite E0 => i?.
      rewrite nth_sub //= /sub_list nth_mkseq //= /nbytes_flatten.
      rewrite (nth_flatten witness n).
         * pose P := (fun (s0 : W8.t list) => size s0 = n).
           pose L := (map NBytes.val (put stack (to_uint (_offset_ - (of_int 2)%W64)) ((insubd (to_list node)))%NBytes)).
           rewrite -(all_nthP P L witness) /P /L size_map => ??.       
           by rewrite (nth_map witness) // valP.
      rewrite (nth_map witness).
      rewrite size_put 1:/#.
      case (0 <= to_uint (_offset_ - (of_int 2)%W64) < size stack) => [Hin | Hout];
      [rewrite nth_put // | rewrite put_out //]; last first.
         * rewrite H4 1:/# //. 
             - rewrite n_val. admit.
(* ! (to_uint ((_offset_ - (of_int 2)%W64) * (of_int 32)%W64) <= i &&
   i < to_uint ((_offset_ - (of_int 2)%W64) * (of_int 32)%W64) + 32) *)
           have ->: _stack.[i] = 
                    nth witness (sub _stack 0 (n * min (to_uint _offset_) (size stack))) i 
                    by rewrite E0 n_val nth_sub.
           by rewrite H2 E0 /sub_list nth_mkseq 1:/# /= nth_nbytes_flatten 1:/#.
         * case (to_uint (_offset_ - (of_int 2)%W64) = i %/ n) => ?.
             + rewrite insubdK; first by rewrite /P size_to_list n_val.
               rewrite get_to_list. admit.
             + rewrite H4 1:/#. admit.
               have ->: _stack.[i] = 
                        nth witness (sub _stack 0 (n * min (to_uint _offset_) (size stack))) i 
                        by rewrite E0 n_val nth_sub.
               by rewrite H2 E0 /sub_list nth_mkseq 1:/# /= nth_nbytes_flatten 1:/#.

qed.

       
