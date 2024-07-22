pragma Goals : printall.

require import AllCore List RealExp IntDiv.
from Jasmin require import JModel.

require import RandomBytes XMSS_IMPL XMSS_IMPL_HOP1.
require import Address Notation Primitives XMSS_MT_PRF.

require import Array8 Array32 Array64 Array128.
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


search Array64.init.

op thash_encode (_left _right : W8.t Array32.t) : W8.t Array64.t = 
    Array64.init (fun (i : int) => if 0 <= i < 32 then _left.[i] else _right.[i-32]).



lemma thash_rand_hash ( _left _right : W8.t Array32.t, _seed : W8.t Array32.t, _addr : W32.t Array8.t) :
    equiv[ 
      M_Hop1(Syscall).__thash_h ~ RandHash.rand_hash : 
      arg{1}.`2 = (thash_encode _left _right) /\ 
      arg{1}.`3 = _seed /\ 
      arg{1}.`4 = _addr /\
      arg{2} = (to_list _left, to_list _right, to_list _seed, _addr)
      ==> 
      res{2}.`1 = to_list res{1}.`1 /\ res{1}.`2 = res{2}.`2
    ].
proof.
proc.
auto => />. move => &1 &2. 
auto => />. (* simplify before moving to the context *)
move => addrL bufL *. do split.
  + admit.
  + admit.
admit.
qed.

