pragma Goals : printall.

require import AllCore List RealExp IntDiv.
from Jasmin require import JModel.

require import XMSS_IMPL_PP XMSS_IMPL.
require import Address Notation Primitives XMSS_MT_PRF.

require import Array8 Array32 Array64.
(*---*) import NBytes.

require import Utils. (* valid_ptr *)

pred array32_list_eq (x : W8.t Array32.t) (y : W8.t list) = 
  forall (k : int), 0 <= k < 32 => x.[k] = nth witness y k.

axiom hash_ptr (mem : global_mem_t) (ptr inlen : W64.t) :
  array32_list_eq (Hash_ptr ptr inlen) (Hash (mkseq (fun (i : int) => loadW8 mem ((W64.to_uint ptr) + i)) (to_uint inlen))).


op addr_to_bytes (a : W32.t Array8.t) : W8.t Array32.t.

(* PRF *)
(* Spec: op PRF : seed -> adrs -> key. *)
(* IMPL: op _PRF_ : W8.t Array32.t -> W8.t Array32.t -> W8.t Array32.t -> W8.t Array32.t. *)
op _PRF_ : W8.t Array32.t -> W8.t Array32.t -> W8.t Array32.t -> W8.t Array32.t.

axiom prf_equiv (out : W8.t Array32.t, addr : W32.t Array8.t, seed : W8.t Array32.t) :
  PRF (to_list seed) addr = to_list (_PRF_ out (addr_to_bytes addr) seed).


(* spec: op F : key -> nbytes -> nbytes. *)
(* impl: op Hash : W8.t list -> W8.t list.*)
axiom hash_F_equiv (a : key, b : nbytes) : F a b = Hash (a ++ b).


lemma thash_f_correct (_out_ : W8.t Array32.t, _pub_seed_ : W8.t Array32.t, _addr_ : W32.t Array8.t) :
    equiv [Mp(Syscall).__thash_f ~ Chain.thash :
      arg{1}=(_out_, _pub_seed_, _addr_) /\ arg{2}=(to_list _out_, _addr_, to_list _pub_seed_) ==>
       res{2}.`1 = to_list res{1}.`1 /\ res{1}.`2 = res{2}.`2].
proof.
proc.
auto => />.
- move => &1 &2 * ; split.
  + admit.
  + admit.
- admit.
qed.

lemma thash_rand_hash (_out : W8.t Array32.t, _in : W8.t Array64.t, _seed : W8.t Array32.t, _addr : W32.t Array8.t) :
    hoare[Mp(Syscall).__thash_h : 
      arg = (_out, _in, _seed, _addr) ==> 
          res.`1 = Array32.of_list witness (rand_hash (to_list _out) (to_list _in) (to_list _seed) _addr).`1].
proof.
proc.
auto => />.
- move => &hr H0 addr buf H1. congr. rewrite /rand_hash. admit.
- while (
  0 <= to_uint i <= 64
) ; auto => />.
    + progress. 
      * rewrite to_uintD /#.
      * rewrite to_uintD_small ; smt(@W64).
    + progress. congr. rewrite /rand_hash. admit.
    + admit.
qed.

