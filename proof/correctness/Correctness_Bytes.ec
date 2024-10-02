pragma Goals : printall.

require import AllCore List RealExp IntDiv.
from Jasmin require import JModel.

require import XMSS_IMPL.

require import Array2 Array32.

require import Hash.
require import Termination.

require import Utils2.

(** -------------------------------------------------------------------------------------------- **)

lemma _ull_to_bytes_32_correct (x : W64.t) : 
    hoare [M(Syscall).__ull_to_bytes_32 :
      arg.`2 = x ==> to_list res = lenbytes_be64 x 32].
proof.
admit. 
qed.

lemma ull_to_bytes_32_correct (x : W64.t) : 
    phoare [M(Syscall).__ull_to_bytes_32 :
      arg.`2 = x ==> to_list res = lenbytes_be64 x 32] = 1%r
        by conseq ull_to_bytes_32_ll (_ull_to_bytes_32_correct x).

(** -------------------------------------------------------------------------------------------- **)

lemma _bytes_to_ull_ptr_correct (mem : global_mem_t) (ptr : W64.t) :
    hoare[
      M(Syscall).__bytes_to_ull_ptr :
      valid_ptr_i ptr 4 /\ arg=ptr 
      ==> 
      res = W64ofBytes (mkseq (fun i => loadW8 mem (to_uint ptr + i)) 4)
    ].
proof.
proc => /=.
while (
  #pre /\
  0 <= to_uint i <= 4 (* /\ ?????? *)
).
    + admit.
    + admit.
qed.

lemma bytes_to_ull_ptr_correct (mem : global_mem_t) (ptr : W64.t) :
    phoare[
      M(Syscall).__bytes_to_ull_ptr :
      valid_ptr_i ptr 4 /\ arg=ptr 
      ==> 
      res = W64ofBytes (mkseq (fun i => loadW8 mem (to_uint ptr + i)) 4)
    ] = 1%r.
proof.
by conseq bytes_to_ull_ptr_ll (_bytes_to_ull_ptr_correct mem ptr). 
qed.

(*
lemma ull_to_bytes_2_correct (y : W64.t) :
    hoare [M(Syscall).__ull_to_bytes_2 : 
      arg.`2 = y ==> 
        to_list res = toByte (W32.of_int (to_uint y)) 2].
proof.
proc.
admit.
qed.

lemma ull_to_bytes_2_ll : islossless M(Syscall).__ull_to_bytes_2
    by proc; while (true) (i - aux); auto => /> /#.

lemma ull_to_bytes_2_equiv (y : W64.t) :
    phoare [M(Syscall).__ull_to_bytes_2 : 
      arg.`2 = y ==> 
        to_list res = toByte (W32.of_int (to_uint y)) 2] = 1%r
          by conseq ull_to_bytes_2_ll (ull_to_bytes_2_correct y) => //.
*)
