pragma Goals : printall.

require import AllCore List RealExp IntDiv.

from Jasmin require import JModel.

require import Array128 Array4.
require import XMSS_IMPL.

require import Array128 Array4.
require import XMSS_IMPL.

lemma memset_4_post (input : W8.t Array4.t, v : W8.t) :
    hoare [M(Syscall).__memset_u8_4 : arg=(input, v) ==> 
     (forall (k : int), 0 <= k < 4 => (res.[k] = v))].
proof.
proc.
while (
  0 <= to_uint i <= 4 /\ 
  value = v /\
  (forall (k : int), 0 <= k < to_uint i => (a.[k] = value))
); auto => /> *.
- do split.
  + smt(@W64).
  + smt(@W64).
  + move => ???. rewrite get_setE ; smt(@W64).
- progress ; [ smt(@W64) | smt ].
qed.

lemma memset_128_post (input : W8.t Array128.t, v : W8.t) :
    hoare [M(Syscall).__memset_u8_128 : arg=(input, v) ==> 
     (forall (k : int), 0 <= k < 128 => (res.[k] = v))].
proof.
proc.
while (
  0 <= to_uint i <= 128 /\ 
  value = v /\
  (forall (k : int), 0 <= k < to_uint i => (a.[k] = value))
); auto => /> *.
- do split.
  + smt(@W64).
  + smt(@W64).
  + move => ???. rewrite get_setE ; smt(@W64).
- progress ; [ smt(@W64) | smt ].
qed.

lemma memset_4_ll : islossless M(Syscall).__memset_u8_4.
proof.
proc.
while (0 <= to_uint i <= 4) (4 - (to_uint i)) ; auto => /> * ; last by smt(@W64).
do split; 1,3: by rewrite to_uintD_small /#. smt(@W64).
qed.

lemma memset_128_ll : islossless M(Syscall).__memset_u8_128.
proof.
proc.
while (0 <= to_uint i <= 128) (128 - (to_uint i)) ; auto => /> * ; last by smt(@W64).
do split; 1,3: by rewrite to_uintD_small /#. smt(@W64).
qed.
