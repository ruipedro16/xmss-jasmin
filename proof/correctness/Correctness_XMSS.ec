pragma Goals : printall.

(**********************************************************************************************************************)

(* proof that the extracted EasyCrypt is equiavalent to the (preprocessed)1 EasyCrypt *)
(* The preprocessed EasyCrypt is the same as the extracted EasyCrypt, but replaces calls to core_hash with calls
   to an operator H *)

require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel.

require import Array32 Array68 Array96 Array128 Array136.

require import XMSS_IMPL XMSS_IMPL_PP.

op Hash_96 : W8.t Array32.t -> W8.t Array96.t -> W8.t Array32.t.
op Hash_128 : W8.t Array32.t -> W8.t Array128.t -> W8.t Array32.t.
op Hash_ptr : W8.t Array32.t -> W64.t -> W64.t -> W8.t Array32.t.

(**********************************************************************************************************************)

axiom hash_96 (out : W8.t Array32.t, in_0 : W8.t Array96.t) :   
   hoare[M(Syscall).__core_hash_96 : arg = (out, in_0) ==> res = Hash_96 out in_0].   

axiom hash__96 (out : W8.t Array32.t, in_0 : W8.t Array96.t) :   
   hoare[M(Syscall)._core_hash_96 : arg = (out, in_0) ==> res = Hash_96 out in_0].   

axiom hash_128 (out : W8.t Array32.t, in_0 : W8.t Array128.t) :   
   hoare[M(Syscall).__core_hash_128 : arg = (out, in_0) ==> res = Hash_128 out in_0].   

axiom hash__128 (out : W8.t Array32.t, in_0 : W8.t Array128.t) :   
   hoare[M(Syscall)._core_hash_128 : arg = (out, in_0) ==> res = Hash_128 out in_0].   

(**********************************************************************************************************************)

lemma xmss_keypair_jazz_equiv (_pk : W8.t Array68.t, _sk : W8.t Array136.t) :
equiv[M(Syscall).xmss_keypair_jazz ~ Mp(Syscall).xmss_keypair_jazz : true ==> ={res}].
proof.
proc.
auto => />.
admit.
qed.
