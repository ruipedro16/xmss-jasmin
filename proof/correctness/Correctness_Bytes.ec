pragma Goals : printall.

require import AllCore List RealExp IntDiv.
from Jasmin require import JModel.

require import XMSS_IMPL.

require import Array2 Array3 Array32.

require import Address Hash BaseW.
require import Termination.

require import Parameters.

require import Utils2.

require import BitEncoding.
(*---*) import BitChunking.

require import StdBigop. 
(*---*) import Bigint.


(** -------------------------------------------------------------------------------------------- **)

lemma ull_to_bytes2_post (x : W64.t, y : W32.t) :
  phoare[
    M(Syscall).__ull_to_bytes_2 : 
    arg.`2 = x /\ to_uint x = to_uint y 
    ==>
    to_list res = toByte y 2 ] = 1%r.
proof.
proc.
conseq (
  : _ 
  ==> 
    out.[0] = nth witness (to_list (unpack8 y)) 3 /\
    out.[1] = nth witness (to_list (unpack8 y)) 2
).
    + auto => /> H  out.
      split => [H1 | H1 H2].
        - rewrite -!get_to_list H1 /toByte !nth_take // !nth_rev; 1,2: by rewrite size_to_list.
          by rewrite size_to_list.
        - apply (eq_from_nth witness); first by rewrite size_to_list /toByte size_take // size_rev size_to_list.
          rewrite size_to_list => j?.
          rewrite get_to_list.
          case (j = 0) => [-> | ?].
             * by rewrite H1 /toByte nth_take // nth_rev. 
             * by rewrite (: j = 1) 1:/# H2 /toByte nth_take // nth_rev.

simplify.

unroll 4; unroll 5.

sp 3.
rcondt 1; first by auto.
sp 3.
rcondt 1; first by auto.
sp.
rcondf 1; first by auto.
auto => /> H0  . 
split; first by admit.
    + rewrite /to_list nth_mkseq //= bits8E /=.
      rewrite /truncateu8 H0 of_intE /=.
      rewrite /int2bs /bits2w /=.
      rewrite wordP => i?.
      rewrite !initiE // nth_mkseq // /= to_uintE.
      rewrite /w2bits /bs2int.
      rewrite size_mkseq (: max 0 32 = 32) 1:/#.
      rewrite BIA.big_int /b2i => />.
     
(* 
search foldr.

auto => />.
print BIA.

print BIA.bigi.

search (W8.bits2w (int2bs _ _)).
search int2bs.
search bits2w.

      rewrite wordP => i?.

      case (i = 0) => [-> /= | ?]; last by admit.
print W8.

search (W8.of_int (W32.to_uint _)).


    + rewrite /to_list nth_mkseq //= bits8E.
      rewrite wordP => i?.
      rewrite initiE //=.
      rewrite /truncateu8 to_uint_shr 1:/# H0 of_uintK /=.
      case (i = 0) => [-> /= | ?]; by admit.


      rewrite /(`>>`) of_uintK /= /(`>>>`).




rewrite wordP => j?.
rewrite /unpack8. 
rewrite /truncateu8 to_uint_shr.
    + by rewrite of_uintK. 
rewrite !of_uintK //.
rewrite /to_list.
rewrite nth_mkseq // => />.
rewrite bits8E initiE //.
rewrite H0.
case (j = 0) => [-> | ?]; last by admit.

admit.
*)
admit.
qed.

lemma _ull_to_bytes_32_correct (x : W64.t) : 
    hoare [M(Syscall).__ull_to_bytes_32 :
      arg.`2 = x ==> to_list res = lenbytes_be64 x 32].
proof.
proc => /=.
auto.
(*
  lenbytes_be64 = rev (mkseq (fun (i : int) => (BitsToBytes (w2bits val)).[i]) len).
  BitsToBytes = map W8.bits2w (chunk 8 bits).
*)
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
