pragma Goals : printall.

require import AllCore List.
from Jasmin require import JModel.
require import XMSS_IMPL XMSS_IMPL_PP. 

require import XMSS.

require import Array8 Array32 Array64.

lemma memcmp_true (x y : W8.t Array32.t) :
    x = y => 
        hoare[Mp(Syscall).__memcmp_ : arg = (x, y) ==> res = W64.zero].
proof.
move => ?.
proc ; inline*.
auto => /> *.
while(
  0 <= to_uint i <= 32 /\
  a1 = b1 /\
  acc = W8.zero
) ; auto => /> *.
split ; by smt(@W64).
qed.

require import Array4.

lemma memset_zero_post (a : W8.t Array4.t) :
    hoare [Mp(Syscall).__memset_zero_u8 : true ==> all ((=) W8.zero) res].
proof.
proc.
while (0 <= to_uint i <= 4 /\ forall (k : int), (0 <= k < to_uint i) => a.[k] = W8.zero).
- auto => />. move => &hr H0 H1 H2 H3. do split.
  + rewrite to_uintD_small /#.
  + rewrite to_uintD_small ; [ smt() | smt(@W64) ].
  + move => ???. admit.
- auto => />. split. 
  + move => k /#. 
  + move => a0 i H0 H1 H2 H3. admit.
qed.

lemma memcmp_false (x y : W8.t Array32.t) :
    x <> y =>
        hoare[Mp(Syscall).__memcmp_ : arg = (x, y) ==> res = W64.of_int (-1)].
proof.
move => ?.
proc ; inline*.
auto => />.
while (
  x <> y /\
  0 <= to_uint i <= 32
  (* Invariant about acc *)
  (* acc = foldr (`|`) . zipWith (^) a1 b1 *)
).
admit.
admit.
qed.

(* ---------------------------------------------------------------------------------------------------------- *)

lemma thash_rand_hash (_out : W8.t Array32.t, _in : W8.t Array64.t, _seed : W8.t Array32.t, _addr : W32.t Array8.t) :
    hoare[Mp(Syscall).__thash_h : 
      arg = (_out, _in, _seed, _addr) ==> 
          res.`1 = Array32.of_list witness (rand_hash (to_list _out) (to_list _in) (to_list _seed) _addr)].
proof.
proc.
auto => /> *.
admit.
admit.
qed.
