pragma Goals : printall.

require import AllCore List RealExp IntDiv.

from Jasmin require import JModel.

require import Array4 Array32 Array64 Array128 Array2144.
require import XMSS_IMPL.
require import Utils2. (* valid_ptr predicate *)
require import Termination.

lemma _memcpy_u8u8_2_32_2144_post (_in : W8.t Array2144.t, oi : W64.t):
    hoare [
      M(Syscall).__memcpy_u8u8_2_32_2144 : 
      arg.`2 = _in /\
      arg.`3 = oi /\
      arg.`4 = W64.of_int 32 /\
      0 <= to_uint oi < W32.max_uint /\
      0 <= to_uint (oi + W64.of_int 32) < 2144
      ==>
      to_list res.`1 = sub _in (to_uint oi) 32
    ].
proof.
proc => //=.
while (  
  in_0 = _in /\ 
  bytes = (of_int 32)%W64 /\
  (0 <= to_uint oi < 2144) /\

  0 <= to_uint i <= 32 /\
  in_offset = oi + i /\

  (forall (k : int), 0 <= k < to_uint i => out.[k] = in_0.[to_uint oi + k]) 
).
    + auto => /> &hr H0 H1 H2 H3 H4 H5.  
      do split.
          * rewrite to_uintD /= #smt:(modz_small).
          * move => ?. 
            rewrite to_uintD /= #smt:(@W64 pow2_64).
          * ring.
          * move => k??.
            rewrite get_setE 1:#smt:(@W64).
            case (k = to_uint i{hr}) => H; first by rewrite H to_uintD /#.
            rewrite H4 // #smt:(@W64).
    + auto => /> &hr ????; do split.
          * smt(@W64 pow2_64). 
          * smt().  
          * move => i0 out0 ????. 
            have ->: to_uint i0 = 32 by smt(@W64 pow2_64). 
            move => H. 
            apply (eq_from_nth witness); first by rewrite size_to_list size_sub.
            rewrite size_to_list => j?.
            by rewrite get_to_list H // nth_sub.
qed.

lemma memcpy_u8u8_2_32_2144_post (_in : W8.t Array2144.t, oi :W64.t):
    phoare [
      M(Syscall).__memcpy_u8u8_2_32_2144 : 
      arg.`2 = _in /\
      arg.`3 = oi /\
      arg.`4 = W64.of_int 32 /\
      0 <= to_uint oi < W32.max_uint /\
      0 <= to_uint (oi + W64.of_int 32) < 2144
      ==>
      to_list res.`1 = sub _in (to_uint oi) 32
    ] = 1%r.
proof.
admit.
qed.

lemma _memcpy_u8u8_2_64_2144_post (_in : W8.t Array2144.t, oi : W64.t):
    hoare [
      M(Syscall).__memcpy_u8u8_2_64_2144 : 
      arg.`2 = _in /\
      arg.`3 = oi /\
      arg.`4 = W64.of_int 64 /\
      0 <= to_uint oi < W32.max_uint /\
      0 <= to_uint (oi + W64.of_int 64) < 2144
      ==>
      to_list res.`1 = sub _in (to_uint oi) 64
    ].
proof.
proc => //=.
while (  
  in_0 = _in /\ 
  bytes = (of_int 64)%W64 /\
  (0 <= to_uint oi < 2144) /\

  0 <= to_uint i <= 64 /\
  in_offset = oi + i /\

  (forall (k : int), 0 <= k < to_uint i => out.[k] = in_0.[to_uint oi + k]) 
).
    + auto => /> &hr H0 H1 H2 H3 H4 H5.  
      do split.
          * rewrite to_uintD /= #smt:(modz_small).
          * move => ?. 
            rewrite to_uintD /= #smt:(@W64 pow2_64).
          * ring.
          * move => k??.
            rewrite get_setE 1:#smt:(@W64).
            case (k = to_uint i{hr}) => H; first by rewrite H to_uintD /#.
            rewrite H4 // #smt:(@W64).
    + auto => /> &hr ????; do split.
          * smt(@W64 pow2_64). 
          * smt().  
          * move => i0 out0 ????. 
            have ->: to_uint i0 = 64 by smt(@W64 pow2_64). 
            move => H. 
            apply (eq_from_nth witness); first by rewrite size_to_list size_sub.
            rewrite size_to_list => j?.
            by rewrite get_to_list H // nth_sub.
qed.


lemma memcpy_u8u8_2_64_2144_post (_in : W8.t Array2144.t, oi : W64.t):
    phoare [
      M(Syscall).__memcpy_u8u8_2_64_2144 : 
      arg.`2 = _in /\
      arg.`3 = oi /\
      arg.`4 = W64.of_int 64 /\
      0 <= to_uint oi < W32.max_uint /\
      0 <= to_uint (oi + W64.of_int 64) < 2144
      ==>
      to_list res.`1 = sub _in (to_uint oi) 64
    ] = 1%r.
proof.
admit.
qed.

(** -------------------------------------------------------------------------------------------- **)

lemma or_zero(w0 w1 : W8.t) : 
    (w0 `|` w1 = W8.zero) <=> (w0 = W8.zero /\ w1 = W8.zero).
proof.
split; last first.
  + move => [-> ->].
    by rewrite or0w.
  + rewrite !wordP => H.
    case (w0 = W8.zero).
      * move => -> /= k kb. move : (H k kb) => /= /#. 
      * move => *. have Hk : exists k, 0 <= k < 8 /\ w0.[k]. 
         - move : (W8.wordP w0 W8.zero); smt(W8.zerowE W8.get_out).
        elim Hk => k [kb kval]. move : (H k kb). by rewrite orwE kval.
qed.

lemma xor_eq (w0 w1 : W8.t) :
    w0 `^` w1 = W8.zero => w0 = w1 by smt(@W8). 
    
(** -------------------------------------------------------------------------------------------- **)

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
- do split; 1,2: by smt(@W64). 
  move => ???. 
  rewrite get_setE #smt:(@W64).
- split => [/# |]. 
  move => ?i0???.   
  (have ->: to_uint i0 = 4 by smt(@W64 pow2_64)) => /#. 
qed.

lemma p_memset_4_post (input : W8.t Array4.t, v : W8.t) :
    phoare [M(Syscall).__memset_u8_4 : arg=(input, v) ==> 
     (forall (k : int), 0 <= k < 4 => (res.[k] = v))] = 1%r.
proof.
by conseq memset_4_ll (memset_4_post input v); auto => />.
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
- do split ; 1,2: by smt(@W64). 
  move => ???. 
  rewrite get_setE #smt:(@W64).
- split => [/# |]. 
  move => ?i0???.   
  (have ->: to_uint i0 = 128 by smt(@W64 pow2_64)) => /#.
qed.

lemma p_memset_128_post (input : W8.t Array128.t, v : W8.t) :
    phoare [M(Syscall).__memset_u8_128 : arg=(input, v) ==> 
     (forall (k : int), 0 <= k < 128 => (res.[k] = v))] = 1%r.
proof.
conseq memset_128_ll (memset_128_post input v); auto => />.
qed.

lemma memset_zero_post :
    hoare [M(Syscall).__memset_zero_u8 : true ==> forall (k : int), 0 <= k < 4 => (res.[k] = W8.zero)].
proof.
proc.
while (
  0 <= to_uint i <= 4 /\   
  (forall (k : int), 0 <= k < to_uint i => (a.[k] = W8.zero))
); auto => /> *.
- do split ; 1,2: by smt(@W64).  
  move => ???.
  rewrite get_setE #smt:(@W64).
- split => [/# |]. 
  move => ?i0???.   
  (have ->: to_uint i0 = 4 by smt(@W64 pow2_64)) => /#. 
qed.

lemma p_memset_zero_post :
    phoare[M(Syscall).__memset_zero_u8 : true ==> forall (k : int), 0 <= k < 4 => (res.[k] = W8.zero)] = 1%r.
proof.
conseq memset_zero_ll memset_zero_post.
auto => />.
qed.

lemma _memset_nseq : 
    hoare [
      M(Syscall).__memset_zero_u8 :
      true
      ==>
      to_list res = nseq 4 W8.zero
    ].
proof.
proc.
while (
  0 <= to_uint i <= 4 /\
  forall (k : int), 0 <= k < to_uint i => a.[k] = W8.zero
). 
    + auto => /> *.
      do split; 1,2:smt(@W64).
      move => ???. 
      rewrite get_setE #smt:(@W64).
    + auto => /> &hr ; split => [/# |]. 
      move => ? i???. 
      have ->: to_uint i = 4 by smt(@W64 pow2_64).
      move => ?. 
      apply (eq_from_nth witness); [ rewrite size_to_list size_nseq //= |].
      rewrite size_to_list => *. 
      rewrite nth_nseq 1:/# get_to_list /#.
qed.

lemma memset_nseq : 
    phoare [ M(Syscall).__memset_zero_u8 : true ==>
       to_list res = nseq 4 W8.zero] = 1%r
          by conseq memset_zero_ll _memset_nseq; auto.

lemma memset_ptr_post (ptr : W64.t, len : W64.t, v : W8.t) :
    hoare [M(Syscall).__memset_u8_ptr : 
      0 <= to_uint len < W64.modulus /\
      0 <= to_uint ptr /\ to_uint (ptr + len) < W64.modulus /\ 
      arg=(ptr, len, v) ==>
        forall (k:int), 0 <= k < to_uint len => (loadW8 Glob.mem (W64.to_uint (ptr  + (W64.of_int k)))) = v].
proof.
proc ; auto.
while (
  #pre /\
  0 <= to_uint i <= to_uint inlen /\
  (forall (k : int), 0 <= k < to_uint i => loadW8 Glob.mem ((W64.to_uint _ptr) + k) = v )
) ; last first.

    + auto => /> &hr H0 H1 H2 *; split; 1:smt(@JMemory). 
      move => mem i H3 H4 H5.
      have ->: i = len by smt(@W64).
      move => H6 k??.
      have ->: (to_uint (ptr + (of_int k)%W64)) = (to_uint ptr + k).
         + rewrite to_uintD of_uintK.  
           have ->: k %% W64.modulus = k by admit.
           admit. 
      apply H6 => //=.

    + auto => /> &hr H0 H1 H2 H3 H4 H5 H6 H7; do split. 
       * smt(@W64).
       * smt(@W64).
       * move => k ??. search loadW8. 
         rewrite /loadW8 /storeW8 get_setE //=.
         case (to_uint ptr + k = to_uint (ptr + i{hr})); [smt(@W64) |].
         admit.
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
  in_ptr1  = ptr /\
  0 <= (to_uint ptr) + 32 <= W64.modulus /\
  0 <= to_uint ptr /\
  
  0 <= i <= 32 /\
  0 <= to_uint in_ptr{hr} + 32 <= W64.modulus /\
  forall (k : int), 0 <= k < i => (out1.[k] = loadW8 Glob.mem ((to_uint ptr) + k))
).
    + auto => /> &hr H0 H1 H2 H3 H4 H5 H6 H7 H8C.
      do split; 1,2:smt().
      move => k??.
      rewrite get_setE //=.
      case (k = i{hr}) => E.
          * congr; rewrite E #smt:(@W64 pow2_64).
          * apply H7 => /#.      
    + auto => /> &hr H0 H1 H2. 
      split => [/# | i0 out0 ???]. 
      have ->: i0 = 32 by smt().
      move => H3.
      rewrite tP => j?.
      rewrite initiE //=. 
      by apply H3.
qed.

lemma memcpy_ptr_ll :
    phoare [
      M(Syscall)._x_memcpy_u8u8p : 
      0 <= (to_uint arg.`2) + 32 <= W64.modulus /\
      0 <= to_uint arg.`2 
      ==>
      true
    ] = 1%r.
proof.
proc.
inline; wp; sp.
while (true) (32 - i); auto => /> /#. 
qed.

lemma p_memcpy_ptr_correct (ptr : W64.t):
    phoare [M(Syscall)._x_memcpy_u8u8p : 
      arg.`2 = ptr /\  
      0 <= (to_uint ptr) + 32 <= W64.modulus /\
      0 <= to_uint ptr ==>
        res = Array32.init (fun (i : int) => loadW8 Glob.mem (to_uint ptr + i))] = 1%r.
proof.
by conseq memcpy_ptr_ll (memcpy_ptr_correct ptr).
qed.

lemma _x_memcpy_u8u8_p (x : W8.t Array32.t) :
hoare [M(Syscall)._x_memcpy_u8u8_32_32 : arg.`2 = x ==> res = x].
proof.
proc.
inline.
wp; sp.
while (
  0 <= to_uint i <= 32 /\ 
  (forall (k : int), 0 <= k < to_uint i => (out1.[k] = in_01.[k])) /\

  in_01 = x
).
    + auto => /> &hr H0 H1 H2 H3. 
      do split; 1,2: by smt(@W64).
      move => k??.
      rewrite get_setE 1:#smt:(@W64).
      case (k = to_uint i{hr}) => [/# | *].
      apply H2.
      smt(@W64).
    + skip => /> &hr.
      split => [/# | i0 out10 ???].
      have ->: to_uint i0 = 32 by smt(@W64 pow2_64).
      by rewrite tP.
qed.


lemma _x_memcpy_u8u8_post (x : W8.t Array32.t) :
    phoare [
        M(Syscall)._x_memcpy_u8u8_32_32 : 
          arg.`2 = x ==> res = x] = 1%r
            by conseq _x_memcpy_u8u8_32_32_ll (_x_memcpy_u8u8_p x).

lemma _x_memcpy_u8u8_64_ (x : W8.t Array64.t) :
    hoare [M(Syscall)._x_memcpy_u8u8_64_64 : arg.`2 = x ==> res = x].
proof.
proc. 
inline; wp; sp. 
while (
  in_01 = x /\
  0 <= to_uint i <= 64 /\
  (forall (k : int), 0 <= k < to_uint i => (out1.[k] = x.[k]))
).
    + auto => /> &hr H0 H1 H2 H3.
      do split; 1,2: by smt(@W64). 
      move => k??. 
      rewrite get_setE 1:#smt:(@W64).
      case (k = to_uint i{hr}) => [/# | *].
      apply H2.
      smt(@W64).
    + auto => /> &hr.
      split => [/# | i0 out10 ???].
      have ->: to_uint i0 = 64 by smt(@W64 pow2_64).
      by rewrite tP.
qed.


lemma _x_memcpy_u8u8_64_post (x : W8.t Array64.t) :
    phoare [M(Syscall)._x_memcpy_u8u8_64_64 : arg.`2 = x ==> res = x] = 1%r
      by conseq _x_memcpy_u8u8_64_64_ll (_x_memcpy_u8u8_64_ x).


(******************************************************************************)
(******************               MEMCMP                          *************)
(******************************************************************************)

lemma memcmp_true (x y : W8.t Array32.t) :
    x = y => 
        hoare[M(Syscall).__memcmp : arg = (x, y) ==> res = W8.zero].
proof.
move => xy_eq.
proc.
while(0 <= to_uint i <= 32 /\ a = b /\ acc = W8.zero) ; auto => /> *; smt(@W64).
qed.

lemma p_memcmp_true (x y : W8.t Array32.t) :
    x = y => 
        phoare[M(Syscall).__memcmp : arg = (x, y) ==> res = W8.zero] = 1%r.
proof.
move => H.
(* conseq (memcmp_ll)  (memcmp_true x y). doesnt work *)
admit.
qed.


lemma memcmp_false (x y : W8.t Array32.t) :
    x <> y => 
        hoare[M(Syscall).__memcmp : arg = (x, y) ==> res <> W8.zero].
proof.
move => ?. 
have E : exists (i : int), 0 <= i < 32 => x.[i] <> y.[i] by smt(@Array32). 
proc.
while (
  #pre /\
  (exists (i : int), 0 <= i && i < 32 => x.[i] <> y.[i]) /\
  0 <= to_uint i <= 32 /\ 
  (acc = W8.zero <=> forall (k : int), 0 <= k < to_uint i => x.[k] = y.[k])
). 
    + auto => /> &hr i0???H0. 
      rewrite ultE of_uintK (: 32 %% W64.modulus = 32) 1:/# => ?. 
      do split; 1,2: smt(@W64).       
         * move => ?. 
           have E1 : acc{hr} = W8.zero by smt(or_zero). 
           have E2 : x.[to_uint i{hr}] `^` y.[to_uint i{hr}] = W8.zero by smt(or_zero).
           have E3 : x.[to_uint i{hr}] = y.[to_uint i{hr}] by smt(xor_eq).
           have E4 : forall (k : int), 0 <= k && k < to_uint i{hr} => x.[k] = y.[k] by smt(). 
           rewrite to_uintD_small /#.
         * rewrite to_uintD_small 1:/# (: to_uint W64.one = 1) 1:/# => H.
           rewrite or_zero; split; [rewrite H0 | rewrite H ] => /#.
    + auto => />; split => [/# | ?i0]. 
      rewrite ultE -lezNgt of_uintK //= => [????? ->].
      have ->: to_uint i0 = 32 by smt(). 
      smt(@Array32). 
qed.

lemma p_memcmp_false (x y : W8.t Array32.t) :
    x <> y => 
        phoare[M(Syscall).__memcmp : arg = (x, y) ==> res <> W8.zero] = 1%r.
proof.
admit.
qed.

(* INLEN = 32 /\ OUTLEN = 2144 *)
(* pre: copying all elements of in does not write out of bounds in out *)
(* 0 <= offset + 32 <= 2144 *)
(* 0 <= offset <= 2112 *)
(* same as memcpy(out + offset, in, sizeof(in)); *)
lemma memcpy_offset_1 (_out_ : W8.t Array2144.t, _offset_ : W64.t, _in_ : W8.t Array32.t) :
    hoare [
      M(Syscall).__memcpy_u8u8_offset : 
      arg.`2=_offset_ /\ 
      arg.`3=_in_ /\  
      0 <= to_uint _offset_ <= 2122 
      ==>
      (forall (k : int), 0 <= k < 32 => (res.[to_uint _offset_ + k] = _in_.[k]))
    ].
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

lemma nbytes_copy_inplace_correct (x : W8.t Array2144.t, oo oi : W64.t) :
    hoare [
      M(Syscall).__nbytes_copy_inplace_2144 :
      arg=(x, oo, oi) /\
      0 <= to_uint oo /\
      to_uint oo + 32 < 2144 /\
      0 <= to_uint oi /\
      to_uint oi + 32 < 2144
      ==>
      (forall (k : int), 0 <= k < 32 => res.[to_uint oo + k] = x.[to_uint oi + k]) /\ (* changed regions *)
      (* values outside the range offset_out to offset_out + n - 1 remain unchanged *)
      (forall (k : int), 0 <= k < 2144 => 
          (k < to_uint oo \/ to_uint oo + 32 <= k) =>
             res.[k] = x.[k])

    ].
proof.
proc.
while (
  #pre /\
  0 <= i <= 32 /\
  (forall (k : int), 0 <= k < i => out.[to_uint offset_out + k] = out.[to_uint offset_in + k])
); last by auto => /> /#.  
auto => /> &hr H0 H1 H2 H3 H4 H5 H6 H7. 
do split; 2,3: by smt().
    + rewrite tP => j?. 
      (* rewrite get_setE. *)
      admit. 
    + move => k??. 
      rewrite get_setE; [rewrite to_uintD_small of_uintK #smt:(modz_small) |].
      rewrite get_setE; [rewrite to_uintD_small of_uintK #smt:(modz_small) |].
      admit. 
qed.

lemma _x_memcpy_u8u8_64_32_p (o : W8.t Array64.t) (x : W8.t Array32.t) :
  hoare [M(Syscall)._x_memcpy_u8u8_64_32 :
    arg.`1 = o /\
    arg.`2 = x ==> 
    sub res 0 32 = to_list x /\
    sub res 32 32 = sub o 32 32].
proof.
proc.
inline.
wp. 
while (
  #pre /\
  0 <= to_uint i <= 32 /\
  (forall (k : int), 0 <= k < to_uint i => out1.[k] = x.[k]) /\
  (forall (k : int), 32 <= k < 64 => out1.[k] = o.[k])
).

    + auto => /> &hr ??H0. 
      rewrite ultE of_uintK /= => H1 ?.
      do split.
         * rewrite to_uintD /#.
         * rewrite to_uintD /#.
         * move => k??.
           rewrite get_setE 1:#smt:(@W64 pow2_64).
           case (k = to_uint i{hr}) => [-> |].
              - admit.
              - admit.
         * move => k??.
           rewrite get_setE 1:#smt:(@W64 pow2_64).
           case (k = to_uint i{hr}) => [-> |].
              - admit.
              - rewrite H1 // /#.
    + auto => />; split => [/# |].
      move => i out ???.
      have ->: to_uint i = 32 by smt(@W64 pow2_64).
      move => H0 H1; split.
         * apply (eq_from_nth witness); first by rewrite size_sub // size_to_list.
           rewrite size_sub // => j?.
           by rewrite get_to_list -H0 // nth_sub.
         * apply (eq_from_nth witness); first by rewrite !size_sub.
           rewrite size_sub // => j?.
           by rewrite !nth_sub // H1 1:/#.
qed.

lemma _x_memcpy_u8u8_64_32_post (o : W8.t Array64.t) (x : W8.t Array32.t) :
  phoare [M(Syscall)._x_memcpy_u8u8_64_32 :
    arg.`1 = o /\
    arg.`2 = x ==> 
    sub res 0 32 = to_list x /\
    sub res 32 32 = sub o 32 32
  ] = 1%r
      by conseq _x_memcpy_u8u8_64_32_ll (_x_memcpy_u8u8_64_32_p o x).
