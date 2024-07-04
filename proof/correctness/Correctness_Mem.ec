pragma Goals : printall.

require import AllCore List RealExp IntDiv.

from Jasmin require import JModel.

require import Array4 Array32 Array128.
require import XMSS_IMPL XMSS_IMPL_PP.

require import Utils. (* valid_ptr predicate *)

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
- do split ; 1,2: by smt(@W64). move => ???. rewrite get_setE ; smt(@W64).
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
- do split ; 1,2: by smt(@W64). move => ???. rewrite get_setE ; smt(@W64).
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
- do split ; 1,2: by smt(@W64). move => ???. rewrite get_setE ; smt(@W64).
- progress ; [ smt(@W64) | smt ].
qed.

lemma load_store  (mem : global_mem_t) (ptr : W64.t) (v : W8.t) :
    loadW8 (storeW8 mem (to_uint ptr) v) (to_uint ptr) = v 
      by rewrite /storeW8 /loadW8 get_setE ifT.

lemma memset_ptr_post (ptr : W64.t, len : W64.t, v : W8.t) :
    hoare [Mp(Syscall).__memset_u8_ptr : 
      0 <= to_uint len /\
      0 <= to_uint ptr /\ to_uint (ptr + len) < W64.modulus /\ 
      arg=(ptr, len, v) ==>
        forall (k:int), 0 <= k < to_uint len => (loadW8 Glob.mem (W64.to_uint (ptr  + (W64.of_int k)))) = v].
proof.
proc.
auto.
while (
  #pre /\
  inlen = len /\ value = v /\ _ptr = ptr /\
  0 <= to_uint i <= to_uint inlen /\
  (forall (k : int), 0 <= k < to_uint i => loadW8 Glob.mem ((W64.to_uint _ptr) + k) = v )
) ; auto => />.
- move => &hr * ; do split.
    + rewrite to_uintD /#.
    + smt(@W64).
    + move => k ??. rewrite /loadW8 /storeW8 get_setE //=. admit.
- move => &hr * ; do split.
    + smt().
    + move => mem ????? k *. rewrite /loadW8. admit.
qed.


lemma memcpy_ptr_post (ptr : W64.t, o : W8.t Array32.t):
    hoare [M(Syscall).__memcpy_u8u8p : 
      arg=(o, ptr) /\ valid_ptr ptr (W64.of_int 32) ==>
            forall (k : int), 0 <= k < 32 => res.[k] = loadW8 Glob.mem (to_uint ptr + k)].
proof.
proc.
while (
  #pre /\
  0 <= i <= 32 /\
  (forall (k : int), 0 <= k < i => out.[k] = loadW8 Glob.mem ((to_uint in_ptr) + k))
) ; auto => />.
- move => &hr * ; do split.
    + rewrite /loadW8. admit.
    + smt().
    + smt().
    + move => k *. rewrite /loadW8 get_setE. smt(). case ( k = i{hr}).
      * move => H0. congr. rewrite to_uintD_small ; [ admit | rewrite of_uintK ; congr ; smt() ].
      * move => ? ; smt(@JMemory).
- move => &hr * ; do split ; by smt().
qed.
