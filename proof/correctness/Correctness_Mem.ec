pragma Goals : printall.

require import AllCore List RealExp IntDiv.

from Jasmin require import JModel.

require import Array128 Array4.
require import XMSS_IMPL.

require import Array128 Array4.
require import XMSS_IMPL XMSS_IMPL_PP.

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

lemma memset_zero_post (x : W8.t Array4.t) :
    hoare [Mp(Syscall).__memset_zero_u8 : true ==> forall (k : int), 0 <= k < 4 => (res.[k] = W8.zero)].
proof.
proc.
while (
  0 <= to_uint i <= 4 /\ 
  (forall (k : int), 0 <= k < to_uint i => (a.[k] = W8.zero))
); auto => /> *.
- do split.
  + smt(@W64).
  + smt(@W64).
  + move => ???. rewrite get_setE ; smt(@W64).
- progress ; [ smt(@W64) | smt ].
qed.

lemma load_store mem (ptr : W64.t) (v : W8.t) :
    loadW8 (storeW8 mem (to_uint ptr) v) (to_uint ptr) = v 
      by rewrite /storeW8 /loadW8 get_setE ifT.

lemma memset_ptr_post (ptr : W64.t, len : W64.t, v : W8.t) :
    hoare [Mp(Syscall).__memset_u8_ptr : 
      0 <= to_uint len < W64.max_uint /\ 
      0 <= to_uint ptr + to_uint len < W64.max_uint /\
      0 <= to_uint ptr < W64.max_uint /\
      arg=(ptr, len, v) ==>
        forall (k:int), 0 <= k < to_uint len => (loadW8 Glob.mem (W64.to_uint (ptr  + (W64.of_int k)))) = v].
proof.
proc.
while (
  #pre /\
  (to_uint ptr) <= to_uint _ptr <= (to_uint (ptr + inlen)) /\
  0 <= to_uint i <= to_uint inlen /\
  (forall (k:int), 0 <= k < to_uint i => ((loadW8 Glob.mem (W64.to_uint (_ptr  + (W64.of_int k)))) = value))
).
- auto => /> * ; do split.
    + rewrite to_uintD_small ; smt(@W64).
    + move => ?. rewrite !to_uintD //=. admit.
    + smt(@W64).
    + smt(@W64).
    + move => *. rewrite /storeW8 /loadW8 get_setE ifT //. congr. admit.
- auto ; progress.
    + rewrite to_uintD_small //= ; smt(@W64).
    + smt.
    + admit.
qed.
