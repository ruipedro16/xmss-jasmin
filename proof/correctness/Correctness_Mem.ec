pragma Goals : printall.

require import AllCore List RealExp IntDiv.

from Jasmin require import JModel.

require import Array4 Array32 Array128 Array2144.
require import XMSS_IMPL (* XMSS_IMPL_PP *).

require import Utils. (* valid_ptr predicate *)

(******************************************************************************)
(******************               MEMSET                          *************)
(******************************************************************************)

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
    hoare [M(Syscall).__memset_zero_u8 : true ==> forall (k : int), 0 <= k < 4 => (res.[k] = W8.zero)].
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
    hoare [M(Syscall).__memset_u8_ptr : 
      0 <= to_uint len /\
      0 <= to_uint ptr /\ to_uint (ptr + len) < W64.modulus /\ 
      arg=(ptr, len, v) ==>
        forall (k:int), 0 <= k < to_uint len => (loadW8 Glob.mem (W64.to_uint (ptr  + (W64.of_int k)))) = v].
proof.
proc ; auto.
while (
  0 <= to_uint len /\
  0 <= to_uint ptr /\ 
  to_uint (ptr + len) < W64.modulus /\ 
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

(******************************************************************************)
(******************               MEMCPY                          *************)
(******************************************************************************)

lemma memcpy_ptr_correct (ptr : W64.t):
    hoare [M(Syscall)._x_memcpy_u8u8p : 
      arg.`2 = ptr /\  
      0 <= (to_uint ptr) + 32 <= W64.modulus /\
      0 <= to_uint ptr ==>
        res = Array32.init (fun (i : int) => loadW8 Glob.mem (to_uint ptr + i))].
proof.
proc.
inline * ; wp ; sp.
while (
  0 <= i <= 32 /\
  0 <= to_uint in_ptr{hr} + 32 <= W64.modulus /\
  forall (k : int), 0 <= k < i => (out1.[k] = loadW8 Glob.mem ((to_uint ptr) + k))
) ; auto => />; last first.
- move => &hr *. split ; 1:smt(@JMemory). move => *. rewrite tP ; smt(@JMemory @Array32).
- move => &hr *. split ; 1:smt(). move => k *. rewrite get_setE 1:/#. case (k = i{hr}); last by smt(@JMemory).
  move => E0 ; congr. rewrite E0 to_uintD of_uintK //=. admit. (* overflow *)
qed.

lemma  memcpy_post (x : W8.t Array32.t) :
    hoare [M(Syscall).__memcpy_u8u8_32_32 : arg.`2 = x ==> res = x].
proof.
proc.
while (
  0 <= to_uint i <= 32 /\
  (forall (k : int), 0 <= k < to_uint i => (out.[k] = in_0.[k]))
); last first.
- auto => /> *. split ; 1:smt(). progress. rewrite tP. move => *. smt.
- auto => /> &hr *. do split; 1,2:smt(@W64). move => k *. rewrite get_setE. smt(@W64). case (k = to_uint i{hr}).
    + move => E0 ; by rewrite E0.
    + move => E0. smt.
qed.

lemma _x_memcpy_u8u8_post (x : W8.t Array32.t) :
    hoare [M(Syscall)._x_memcpy_u8u8_32_32 : arg.`2 = x ==> res = x].
proof.
proc ; inline M(Syscall)._memcpy_u8u8_32_32.
wp ; sp ; ecall (memcpy_post in_00) ; skip => />.
qed.


(******************************************************************************)
(******************               MEMCMP                          *************)
(******************************************************************************)

lemma memcmp_true (x y : W8.t Array32.t) :
    x = y => 
        hoare[M(Syscall).__memcmp : arg = (x, y) ==> res = W64.zero].
proof.
move => xy_eq.
proc ; auto => /> *.
while(0 <= to_uint i <= 32 /\  a = b /\  acc = W8.zero) ; auto => /> *; smt(@W64).
qed.

lemma memcmp_false (x y : W8.t Array32.t) :
    x <> y => 
        hoare[M(Syscall).__memcmp : arg = (x, y) ==> res = W64.of_int (-1)].
proof.
move => xy_neq.
proc.
seq 6: (!zf /\ r = W64.of_int (-1)) ; last by auto => />.
wp ; sp.
while (
  0 <= to_uint i <= 32 /\ a <> b
(*  (acc = W8.zero => (forall (j : int), 0 <= j < to_uint i => a.[j] = b.[j])) *)
) ; auto => /> *.
- smt(@W64).
- admit.
qed.

(* INLEN = 32 /\ OUTLEN = 2144 *)
(* pre: copying all elements of in does not write out of bounds in out *)
(* 0 <= offset + 32 <= 2144 *)
(* 0 <= offset <= 2112 *)
(* same as memcpy(out + offset, in, sizeof(in)); *)
lemma memcpy_offset_1 (_out_ : W8.t Array2144.t, _offset_ : W64.t, _in_ : W8.t Array32.t) :
    hoare [M(Syscall).__memcpy_u8u8_offset : 
      arg.`2=_offset_ /\ arg.`3=_in_ /\  0 <= to_uint _offset_ <= 2122 ==>
        (forall (k : int), 0 <= k < 32 => (res.[to_uint _offset_ + k] = _in_.[k]))].
proof.
proc.
sp.
while (
  0 <= to_uint offset <= 2144 /\ (* offset + inlen <= outlen *)
  0 <= to_uint i <= 32 /\
  forall (k : int), 0 <= k < 32 => (out.[to_uint _offset_ + k] = in_0.[k])
) ; last first.
- skip => /> &hr * ; do split.
    + smt(@W64 pow2_64).
    + move => ???. admit. (* smt(@Array32 @Array2144). *) 
- auto => /> &hr * ; do split.
    + smt(@W64).
    + move => ?.  admit.
    + smt(@W64).
    + smt(@W64).
    + move => ???. rewrite get_setE. split ; 1:smt(). move => ?. admit. admit.
qed.


(******************************************************************************)
(******************               MEMSWAP                         *************)
(******************************************************************************)

lemma memswap_post (x y z : W8.t Array32.t) :
    hoare[M(Syscall).__memswap_32 :
      arg=(x, y, z) ==> res.`1=y /\ res.`2=x /\ res.`3=x].
proof.
proc.
seq 1: (a=x /\ b=y /\ t=x); first by ecall (_x_memcpy_u8u8_post a). 
seq 1: (a=y /\ b=y /\ t=x); first by ecall (_x_memcpy_u8u8_post b); skip => />.
seq 1: (a=y /\ b=x /\ t=x); first by ecall (_x_memcpy_u8u8_post t); skip => />.
trivial. 
qed.
