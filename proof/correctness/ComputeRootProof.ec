pragma Goals : printall.

require import AllCore List RealExp IntDiv Distr DList IntDiv.
from Jasmin require import JModel JArray.

require import Types Params Parameters Address WOTS LTree XMSS_MT_TreeHash.
require import XMSS_IMPL.

require import Utils2.

require import Array32 Array64.

op load_nbytes_mem (mem : global_mem_t) (ptr : W64.t) : W8.t Array64.t =
  Array64.init(fun i => loadW8 mem (to_uint ptr + i)).

(* TODO: Factor out the 8 - end steps of {2} to module root_from_sig_inner *)
lemma computeRootCorrect (mem : global_mem_t) : 
    equiv [
      M(Syscall).__compute_root ~ RootFromSig.rootFromSig :
      Glob.mem{1} = mem /\
      Glob.mem{2} = mem /\
      valid_ptr arg{1}.`4 (W64.of_int 32)
      ==>
      to_list res{1}.`1 = val res{2}
    ].
proof.
proc.
seq 0 8 : (#pre); first by admit.
seq 2 0 : #pre; first by auto.
seq 3 0 : (
  #pre /\
  auth_path_ptr{1} = _auth_path_ptr{1} /\
  t32{1} = leaf_idx{1} `&` W32.one 
); first by auto. 
seq 1 0 : (
  #pre /\
  (t32{1} <> W32.zero => to_list buffer{1} = to_list leaf{1} ++ to_list (load_nbytes_mem mem auth_path_ptr{1}) ) /\
  (t32{1} = W32.zero  => to_list buffer{1} = to_list (load_nbytes_mem mem auth_path_ptr{1}) ++ to_list leaf{1} )
).
    + admit.

seq 1 0 : ( 
  Glob.mem{1} = mem /\ 
  Glob.mem{2} = mem /\
  valid_ptr _auth_path_ptr{1} (of_int 32)%W64 /\
  to_uint auth_path_ptr{1} = to_uint _auth_path_ptr{1} + 32 /\ 
  t32{1} = leaf_idx{1} `&` W32.one /\
  (t32{1} <> W32.zero => to_list buffer{1} = to_list leaf{1} ++ to_list (load_nbytes_mem mem auth_path_ptr{1})) /\
  (t32{1} = W32.zero => to_list buffer{1} = to_list (load_nbytes_mem mem auth_path_ptr{1}) ++ to_list leaf{1})
).
    + auto => /> &1 H0 H1 H2 H3.
      do split.
          * admit.
          * admit.
          * admit.
seq 2 2 : #pre.

seq 2 0 : (#pre); last by admit.
    + admit.
admit.


qed.
