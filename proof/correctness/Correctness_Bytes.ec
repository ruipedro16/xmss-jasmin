pragma Goals : printall.

require import AllCore List RealExp IntDiv.
from Jasmin require import JModel.

require import XMSS_IMPL.

require import Array2 Array3 Array32.

require import Address Hash BaseW.
require import Termination.

require import Parameters.

require import Utils2 Repr2.

require import BitEncoding.
(*---*) import BitChunking.

require import StdBigop. 
(*---*) import Bigint.

import W4u8.Pack.

(**  relacao entre o toByte da spec e os outros da impl ------------------------------------------------------------ **)

(** -------------------------------------------------------------------------------------------- **)

lemma ull_to_bytes2_post (x : W64.t, y : W32.t) :
  phoare[
    M(Syscall).__ull_to_bytes_2 : 
    arg.`2 = x /\ 
    to_uint x = to_uint y /\
    0 <= to_uint y < W32.max_uint 
    ==>
    to_list res = toByte y 2 ] = 1%r.
proof.
proc.
unroll 4; unroll 5.
rcondt 4; first by auto.
rcondt 7; first by auto.
rcondf 10; first by auto.
auto => /> &hr H0 H1 H2.
apply (eq_from_nth witness); first by rewrite size_to_list size_toByte_32.
rewrite size_to_list => j?.
rewrite get_to_list.
rewrite /toByte nth_rev.
  + by rewrite size_mkseq.
rewrite nth_mkseq /=.
  + by rewrite !size_mkseq /#.
rewrite size_mkseq (: max 0 2 = 2) //.
case (j = 1) => [-> | ?]; auto => />.
  + rewrite /BitsToBytes.
    rewrite wordP => i [??].
    rewrite (nth_map witness); first by rewrite size_chunk // size_w2bits.
    rewrite /chunk size_w2bits nth_mkseq 1:/# /=.
    rewrite bits2wE initiE //= nth_take // nth_drop //.
    rewrite w2bitsE nth_mkseq 1:/# /=.
    rewrite /truncateu8 H0.
    admit.

  + have ->: j = 0 by smt(). 
    rewrite !get_setE // ifT 1:/#.
    rewrite wordP => i [??].
    rewrite /BitsToBytes.
    rewrite (nth_map witness); first by rewrite size_chunk // size_w2bits.
    rewrite /chunk size_w2bits nth_mkseq 1:/# /=.
    rewrite bits2wE initiE //= nth_take // nth_drop //.
    rewrite w2bitsE nth_mkseq 1:/# /=.
    rewrite /truncateu8 to_uint_shr of_uintK //= H0.
    admit.
qed.

lemma _ull_to_bytes_32_correct (x : W64.t) : 
    hoare [M(Syscall).__ull_to_bytes_32 :
      arg.`2 = x ==> to_list res = toByte_64 x 32].
proof.
proc => /=.
auto.
admit.
qed.

lemma ull_to_bytes_32_correct (x : W64.t) : 
    phoare [
      M(Syscall).__ull_to_bytes_32 :
      arg.`2 = x 
      ==> 
      to_list res = toByte_64 x 32
    ] = 1%r
        by conseq ull_to_bytes_32_ll (_ull_to_bytes_32_correct x).

lemma ull_to_bytes_3_correct (x : W64.t) : 
    phoare [
      M(Syscall).__ull_to_bytes_3 :
      arg.`2 = x 
      ==> 
      to_list res = toByte_64 x 3
    ] = 1%r.
proof.
proc => /=.
admit.
qed.
        


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
      valid_ptr_i ptr XMSS_INDEX_BYTES /\ arg=ptr 
      ==> 
      res = W64ofBytes (mkseq (fun i => loadW8 mem (to_uint ptr + i)) XMSS_INDEX_BYTES)
    ] = 1%r.
proof.
by conseq bytes_to_ull_ptr_ll (_bytes_to_ull_ptr_correct mem ptr). 
qed.

(** -------------------------------------------------------------------------------------------- **)

lemma ull_to_bytes_correct_ (bytes : W8.t Array3.t) : (* the array has the size XMSS_IDX_BYTES *)
   hoare[ M(Syscall).__bytes_to_ull : arg = bytes ==> 
      res = W64ofBytes (to_list bytes)].
proof.
proc => /=.
admit.
qed.

lemma ull_to_bytes_correct (bytes : W8.t Array3.t) : (* the array has the size XMSS_IDX_BYTES *)
   phoare[ M(Syscall).__bytes_to_ull : arg = bytes ==> 
      res = W64ofBytes (to_list bytes)] = 1%r.
proof.
admit.
qed.
