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

lemma l_tree_ll : islossless Mp(Syscall).__l_tree.
proof.
proc.
islossless ; last by admit.
while (0 <= inlen < W64.max_uint) (inlen - to_uint i).
auto => /> *. smt.
auto => /> *. do split.
admit.
admit.
auto => /> *. smt.
qed.

lemma xmss_kg_ll : islossless Mp(Syscall).xmss_keypair_jazz.
proof.
proc.
islossless; 4,9,10: by admit. (* replace with islossless ; last by smt. *)

while (true) (32 - i) => //=; by auto => /> /#. (* 1st subgoal *)
while (true) (32 - i) => //=; by auto => /> /#. (* 2nd subgoal *)
while (true) (32 - j) => //=; by auto => /> /#. (* 3rd subgoal *)
while (true) (8 - i) => //=; by auto => /> /#. (* 5th subgoal *)
while (true) (8 - i) => //=; by auto => /> /#. (* 6th subgoal *)
while (true) (8 - i) => //=; by auto => /> /#. (* 7th subgoal *)
while (0 < inlen < W64.max_uint) (inlen - (to_uint i)). (* 8th subgoal *)
admit.
auto => /> * //=. do split. admit. admit.
auto => /> * //=. admit.
(* 8th subgoal finishes here *)
while (true) (4 - (to_uint i)) ; by auto => /> * ; smt. (* 1th subgoal: *)
while (true) (8 - i) => //= ; by auto => /> /#. (* 12th subgoal *)
smt.
qed.

lemma compute_root_ll : islossless Mp(Syscall).__compute_root.
proof.
proc.
(* islossless. *)
islossless ; 6,8,9,10: by admit.
(* 1st subgoal *)
while (true) (64 - to_uint i) => //=; by auto => /> * ; smt.
(* 2nd subgoal *)
while (true) (8 - i) => //=; last by auto => /#.
auto. inline. auto => /> /#.
(* 3rd subgoal *)
while (true) (8 - i) => //=; last by auto => /#.
auto. inline. auto => /> /#.
(* 4th subgoal *)
while (true) (8 - i) => //=; last by auto => /#.
auto. inline. auto => /> /#.
(* 5th subgoal *)
while (true) (i - aux) => //=; by auto => /#.
(* 6th subgoal *)
(* 7th subgoal *)
while (true) (to_uint inlen - to_uint i) => //=; last by auto => /> /#.
auto => /> *. smt.
qed.
