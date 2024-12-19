pragma Goals : printall.

require import AllCore List RealExp IntDiv.

from Jasmin require import JModel.

require import Array3 Array32 Array64 Array128 Array2144.
require import Array352.

require import XMSS_IMPL.
require import Utils2 Repr2.
require import Termination.

require import Params Parameters. 

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

  sub out 0 (to_uint i) = 
  sub_list 
  (val (nth witness stack_spec (to_uint (o - (of_int 2)%W64))) ++ val (nth witness stack_spec (to_uint (o - W64.one))))
  0 (to_uint i)
); last first.

- auto => /> &hr H0 H1.
  split.
  + apply (eq_from_nth witness); first by rewrite size_sub // size_sub_list.      
    rewrite size_sub // /#.
  + move => j out0.
    rewrite ultE of_uintK /= => ???.
    have ->: to_uint j = 64 by smt().
    move => H.
    apply (eq_from_nth witness); first by rewrite size_to_list size_cat !valP n_val.
    rewrite size_to_list => i?.
    have ->: to_list out0 = sub out0 0 64.
       * apply (eq_from_nth witness); first by rewrite size_to_list size_sub.
         rewrite size_to_list => ??.
         by rewrite get_to_list nth_sub.
    rewrite H.
    by rewrite /sub_list nth_mkseq.

- auto => /> &hr H0 H1 H2 H3 H4.
  rewrite ultE of_uintK /= => H5.
  do split.
  + ring.
  + rewrite to_uintD /#.
  + rewrite to_uintD /#.
  + apply (eq_from_nth witness).
       * rewrite size_sub; first by rewrite to_uintD /#.
         rewrite size_sub_list; first by rewrite to_uintD /#.
         reflexivity.
    rewrite size_sub; first by rewrite to_uintD /#.
    rewrite to_uintD_small 1:/# /= => j?.
    rewrite nth_sub //= /sub_list nth_mkseq //=.
    case (2 <= to_uint o < size stack_spec) => [H_in_bounds | H_out_of_bounds]; last by admit.
    (* ============== case in bounds ============ *)    
    have E0 : min (to_uint o) (size stack_spec) = to_uint o by smt().
    move: H1; rewrite E0 => H1.
    case (0 <= j < 32) => ?; 
       rewrite nth_cat valP n_val; [rewrite ifT 1:/# | rewrite ifF 1:/#];
       rewrite get_setE 1:/#;
       case (j = to_uint i{hr}) => [-> | ? | -> | ?]. 
       * admit.
       * have ->: out{hr}.[j] = nth witness (sub out{hr} 0 (to_uint i{hr})) j by rewrite nth_sub // /#.
         rewrite H4 /sub_list nth_mkseq 1:/# //= nth_cat ifT.
            + rewrite valP /#.
         by congr; rewrite valP n_val.
       * admit.
       * have ->: out{hr}.[j] = nth witness (sub out{hr} 0 (to_uint i{hr})) j by rewrite nth_sub // /#.
         rewrite H4 /sub_list nth_mkseq 1:/# //= nth_cat ifF.
            + rewrite valP /#.
         by congr; rewrite valP n_val.
         
 

    (* ============== case out of bounds ============ *)      

