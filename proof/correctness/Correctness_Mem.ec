pragma Goals : printall.

require import AllCore List RealExp IntDiv.

from Jasmin require import JModel.

require import Array3 Array32 Array64 Array128 Array2144.
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
proc => //=.
while (  
  in_0 = _in /\ 
  bytes = (of_int 32)%W64 /\
  (0 <= to_uint oi < 2144) /\

  0 <= to_uint i <= 32 /\
  in_offset = oi + i /\

  (forall (k : int), 0 <= k < to_uint i => out.[k] = in_0.[to_uint oi + k]) 
)
(32 - to_uint i).

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
          * rewrite to_uintD /#.
    + auto => /> &hr ????; do split.
          * smt(@W64 pow2_64). 
          * smt().  
          * move => i0 out0. 
            split => ????; [by rewrite ultE of_uintK /# |].
            have ->: to_uint i0 = 32 by smt(@W64 pow2_64). 
            move => H. 
            apply (eq_from_nth witness); first by rewrite size_to_list size_sub.
            rewrite size_to_list => j?.
            by rewrite get_to_list H // nth_sub.
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
proc => /=. 
while (
  #{/~in_offset = oi}pre /\ 
  to_uint in_offset = to_uint oi + to_uint i /\  
  0 <= to_uint i <= to_uint bytes /\
  sub out 0 (to_uint i) = sub _in (to_uint oi) (to_uint i)
)
(to_uint bytes - to_uint i); last first.
  + auto => /> &hr H0 H1 H2 H3. 
    split.
      - apply (eq_from_nth witness); first by rewrite !size_sub.    
        rewrite size_sub /#.
      - move => i0 out0. 
        rewrite ultE of_uintK /=.
        move => out0_0.
        split => [/# |].
        move => H4 H5 H6 H7.
        have ->: to_uint i0 = 64 by smt().
        move => <-.
        apply (eq_from_nth witness); first by rewrite size_to_list size_sub.
        rewrite size_to_list => ??.
        by rewrite get_to_list nth_sub. 
    + auto => /> &hr.
      rewrite ultE of_uintK /= => H0 H1 H2 H3 H4 H5 H6 H7 H8. 
      do split; 2,3,5: by rewrite to_uintD /#.
          - rewrite !to_uintD_small 1,2:/# H4 /#.
          - apply (eq_from_nth witness); first by rewrite !size_sub to_uintD /#.
            rewrite size_sub to_uintD_small 1..3:/# /= => j?.
            rewrite !nth_sub //= get_setE //.
            case (j = to_uint i{hr}) => [-> /# |?]. 
            have ->: out{hr}.[j] = nth witness (sub out{hr} 0 (to_uint i{hr})) j by rewrite nth_sub /#.
            rewrite H7.
            rewrite nth_sub // /#.
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

lemma memset_4_post (input : W8.t Array3.t, v : W8.t) :
    hoare [M(Syscall).__memset_u8_3 : arg=(input, v) ==> 
     (forall (k : int), 0 <= k < 3 => (res.[k] = v))].
proof.
proc.
while (
  0 <= to_uint i <= 3 /\ 
  value = v /\
  (forall (k : int), 0 <= k < to_uint i => (a.[k] = value))
); auto => /> *.
- do split; 1,2: by smt(@W64). 
  move => ???. 
  rewrite get_setE #smt:(@W64).
- split => [/# |]. 
  move => ?i0???.   
  (have ->: to_uint i0 = 3 by smt(@W64 pow2_64)) => /#. 
qed.

lemma p_memset_4_post (input : W8.t Array3.t, v : W8.t) :
    phoare [M(Syscall).__memset_u8_3 : arg=(input, v) ==> 
     (forall (k : int), 0 <= k < 3 => (res.[k] = v))] = 1%r.
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
    hoare [M(Syscall).__memset_zero_u8 : true ==> forall (k : int), 0 <= k < 3 => (res.[k] = W8.zero)].
proof.
proc.
while (
  0 <= to_uint i <= 3 /\   
  (forall (k : int), 0 <= k < to_uint i => (a.[k] = W8.zero))
); auto => /> *.
- do split ; 1,2: by smt(@W64).  
  move => ???.
  rewrite get_setE #smt:(@W64).
- split => [/# |]. 
  move => ?i0???.   
  (have ->: to_uint i0 = 3 by smt(@W64 pow2_64)) => /#. 
qed.

lemma p_memset_zero_post :
    phoare[M(Syscall).__memset_zero_u8 : true ==> 
      forall (k : int), 0 <= k < 3 => (res.[k] = W8.zero)] = 1%r.
proof.
conseq memset_zero_ll memset_zero_post.
auto => />.
qed.

lemma _memset_nseq : 
    hoare [
      M(Syscall).__memset_zero_u8 :
      true
      ==>
      to_list res = nseq 3 W8.zero
    ].
proof.
proc.
while (
  0 <= to_uint i <= 3 /\
  forall (k : int), 0 <= k < to_uint i => a.[k] = W8.zero
). 
    + auto => /> *.
      do split; 1,2:smt(@W64).
      move => ???. 
      rewrite get_setE #smt:(@W64).
    + auto => /> &hr ; split => [/# |]. 
      move => ? i???. 
      have ->: to_uint i = 3 by smt(@W64 pow2_64).
      move => ?. 
      apply (eq_from_nth witness); [ rewrite size_to_list size_nseq //= |].
      rewrite size_to_list => *. 
      rewrite nth_nseq 1:/# get_to_list /#.
qed.

lemma memset_nseq : 
    phoare [ M(Syscall).__memset_zero_u8 : true ==>
       to_list res = nseq 3 W8.zero] = 1%r
          by conseq memset_zero_ll _memset_nseq; auto.

lemma memset_ptr_post (ptr : W64.t, len : W64.t, v : W8.t) :
    hoare [M(Syscall).__memset_u8_ptr : 
      0 <= to_uint len < W64.modulus /\
      0 <= to_uint ptr /\ to_uint ptr + to_uint len < W64.modulus /\ 
      arg=(ptr, len, v) ==>
        forall (k:int), 0 <= k < to_uint len => (loadW8 Glob.mem (W64.to_uint (ptr  + (W64.of_int k)))) = v].
proof.
proc => /=.
while (
  #pre /\
  0 <= to_uint i <= to_uint inlen /\
  (forall (k : int), 0 <= k < to_uint i => loadW8 Glob.mem ((W64.to_uint _ptr) + k) = v )
); last first.
    + auto => /> &hr H0 H1 H2 H3.
      split => [/# |].
      move => mem j.
      rewrite ultE => H4 H5 H6.
      have ->: j = len by smt(@W64 pow2_64).
      move => H7 k??.
      rewrite /loadW8 to_uintD_small of_uintK /#. 
    + auto => /> &hr H0 H1 H2 H3 H4 H5 H6.
      rewrite ultE => H7.
      do split.
         - rewrite to_uintD /#.
         - rewrite to_uintD /#.
         - rewrite to_uintD_small 1:/# => k??.
           rewrite /loadW8 /storeW8 get_setE. 
           case (k = to_uint i{hr}) => [-> |?].
              + rewrite ifT // to_uintD /#.
              + rewrite ifF; [rewrite to_uintD /# |].
                rewrite /loadW8 in H6.
                apply H6.
                smt(@W64 pow2_64).
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


(* conseq is not working here so i wrote the proof twice *)
lemma p_memcmp_true (x y : W8.t Array32.t) :
    x = y => 
        phoare[M(Syscall).__memcmp : arg = (x, y) ==> res = W8.zero] = 1%r.
proof.
move => ?.
proc.
while(0 <= to_uint i <= 32 /\ a = b /\ acc = W8.zero) (32 - to_uint i); auto => /> *; smt(@W64).
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
move => ?. 
have E : exists (i : int), 0 <= i < 32 => x.[i] <> y.[i] by smt(@Array32). 
proc.
while (
  #pre /\
  (exists (i : int), 0 <= i && i < 32 => x.[i] <> y.[i]) /\
  0 <= to_uint i <= 32 /\ 
  (acc = W8.zero <=> forall (k : int), 0 <= k < to_uint i => x.[k] = y.[k])
)
(32 - to_uint i). 
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
         * smt(@W64 pow2_64).
    + auto => />; split => [/# | ?i0]. 
      rewrite ultE -lezNgt of_uintK //=; split => [|????? ->]; first by smt(@W64 pow2_64).
      have ->: to_uint i0 = 32 by smt(). 
      smt(@Array32). 
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
      0 <= to_uint _offset_ < (2144 - 32)
      ==>
      (forall (k : int), 0 <= k < 32 => (res.[to_uint _offset_ + k] = _in_.[k]))
    ].
proof.
(* Easier to read #post *)
conseq (: _ ==> sub res (to_uint _offset_) 32 = sub _in_ 0 32).
  + auto => /> &hr H0 H1 result H2 k??.
    have ->: in_0{hr}.[k] = nth witness (sub in_0{hr} 0 32) k by rewrite nth_sub.
    by rewrite -H2 nth_sub.
proc => /=.
while (
  #{/~offset = _offset_}pre /\
  0 <= to_uint i <= 32 /\
  offset = _offset_ + i /\
  sub out (to_uint _offset_) (to_uint i) = sub _in_ 0 (to_uint i)  
); last first.
    + auto => /> &hr H0 H1. 
      do split.
         - apply (eq_from_nth witness); first by rewrite !size_sub.
           rewrite size_sub // /#.
         - move => i0 out0.
           rewrite ultE of_uintK /= => H2 H3 H4.
           have ->: to_uint i0 = 32 by smt().
           by move => ->.
    + auto => /> &hr H0 H1 H2 H3 H4.
      rewrite ultE of_uintK /= => H5.
      do split. 
          - rewrite to_uintD /#.
          - rewrite to_uintD /#.
          - by ring.
          - apply (eq_from_nth witness); first by rewrite !size_sub to_uintD /#.
            rewrite size_sub to_uintD 1:/# /= => j?.
            rewrite !nth_sub //= get_setE //; [rewrite to_uintD /# |].
            case (j = to_uint i{hr}) => [-> |?].
                - by rewrite ifT // to_uintD /#.
                - rewrite ifF; first rewrite to_uintD /#.
                  have ->: _in_.[j] = nth witness (sub _in_ 0 (to_uint i{hr})) j by rewrite nth_sub // /#. 
                  rewrite -H4 nth_sub /#.
qed.

(* FIXME: Nova precondicao: oo + 32 e ii + 32 sao disjuntos *)
lemma nbytes_copy_inplace_correct (x : W8.t Array2144.t, oo oi : W64.t) :
    hoare [
      M(Syscall).__nbytes_copy_inplace_2144 :
      arg=(x, oo, oi) /\
      0 <= to_uint oo /\
      to_uint oo + 32 < 2144 /\
      0 <= to_uint oi /\
      to_uint oi + 32 < 2144
      ==>
      sub res (to_uint oo) 32 = sub x (to_uint oi) 32 /\
      (forall (k : int), 0 <= k < to_uint oo => res.[k] = x.[k]) /\
      (forall (k : int), to_uint oo + 32 <= k < 2144 => res.[k] = x.[k])
      (* values outside the range offset_out to offset_out + n - 1 remain unchanged *)
      ].
proof.
proc => /=.  
while (
  #{/~out = x}pre /\
  0 <= i <= 32 /\
  sub out (to_uint oo) i = sub x (to_uint oi) i /\
  (forall (k : int), 0 <= k < to_uint oo => out.[k] = x.[k]) /\
  (forall (k : int), to_uint oo + i <= k < 2144 => out.[k] = x.[k])

); last first.
    + auto => /> H0 H1 H2 H3.
      split => [| /#].
      apply (eq_from_nth witness); first by rewrite !size_sub.
      rewrite size_sub /#.
auto => /> &hr H0 H1 H2 H3 H4 H5 H6 H7 H8 H9.
do split;4..5: by admit.
    + smt().
    + smt().
    + apply (eq_from_nth witness); first by rewrite !size_sub /#.
      rewrite size_sub 1:/# => j?.
      rewrite !nth_sub 1,2:/# get_setE; first by rewrite to_uintD of_uintK /#.
      case(j = i{hr}) => [-> | //?]; last first.
         + rewrite ifF; first by rewrite to_uintD of_uintK /#.
           have ->: x.[to_uint oi + j] = nth witness (sub x (to_uint oi) i{hr}) j by rewrite nth_sub /#.
           rewrite -H6 nth_sub /#.
      rewrite ifT; first by rewrite to_uintD of_uintK /#.
      have ->: to_uint (oi + (of_int i{hr})%W64) = to_uint oi + i{hr} by rewrite to_uintD of_uintK /#.
      case (0 <= to_uint oi + i{hr} < to_uint oo) => Ha.
          + rewrite H7 /#. 
      case (to_uint oo + i{hr} < 2144) => Hb.
rewrite H8 //. have E: 0 <= i{hr} < 32 by smt().
      admit
.
      admit.
qed.

lemma _x_memcpy_u8u8_64_32_p (o : W8.t Array64.t) (x : W8.t Array32.t) :
  hoare [M(Syscall)._x_memcpy_u8u8_64_32 :
    arg.`1 = o /\
    arg.`2 = x 
    ==> 
    to_list res = (to_list x) ++ sub o 32 32
  ].
proof.
proc => /=.
inline.
wp; sp 6.
while (
  #{/~ out1 = out0}pre /\
  0 <= to_uint i <= 32 /\
  sub out1 0 (to_uint i)  = sub x 0 (to_uint i) /\
  sub out1 (to_uint i) (64 - to_uint i) = sub o (to_uint i) (64 - to_uint i)
); last first.
    + auto => />. 
      split.
        -  apply (eq_from_nth witness); first by rewrite !size_sub.
           rewrite size_sub // /#.
        - move => j outj.
          rewrite ultE of_uintK /= => H0 H1 H2 H3 H4.
          apply (eq_from_nth witness); first by rewrite size_cat !size_to_list size_sub.
          rewrite size_to_list => ii ?.
          case (0 <= ii < 32) => H. 
            + rewrite nth_cat size_to_list ifT 1:/# get_to_list.
              have ->: outj.[ii] = nth witness (sub outj 0 (to_uint j)) ii by rewrite nth_sub /#.
              by rewrite H3 nth_sub 1:/# get_to_list.
          rewrite nth_cat size_to_list ifF 1:/# get_to_list nth_sub 1:/# /=.
          have ->: o.[ii] = nth witness (sub o (to_uint j) (64 - to_uint j)) (ii - to_uint j) by rewrite nth_sub /#.
          rewrite -H4 nth_sub /#.
    + auto => /> &hr H0 H1 H2 H3.
      rewrite ultE of_uintK /= => H4.
      do split.
        - rewrite to_uintD /#.
        - rewrite to_uintD /#.
        - apply (eq_from_nth witness); [rewrite !size_sub; 1..3: by rewrite to_uintD /# |].
          rewrite size_sub; [rewrite to_uintD /#|].
          have ->: to_uint (i{hr} + W64.one) = to_uint i{hr} + 1 by rewrite to_uintD /#.
          move => j?.
          rewrite !nth_sub //= get_setE 1:/#.
          case (j = to_uint i{hr}) => [-> // | // ?]. (* Obs: move => -> // solves the first subgoal, thats why we only have one subgoal after case *)
          have ->: x.[j] = nth witness (sub x 0 (to_uint i{hr})) j by rewrite nth_sub // /#.
          rewrite -H2 nth_sub /#.
        - apply (eq_from_nth witness); first by rewrite !size_sub to_uintD /#.
          rewrite size_sub; [rewrite to_uintD /# |].
          have ->: to_uint (i{hr} + W64.one) = to_uint i{hr} + 1 by rewrite to_uintD /#.
          move => j?.
          rewrite !nth_sub // get_setE 1:/# ifF 1:/#. 
          have ->: o.[to_uint i{hr} + 1 + j] = nth witness (sub o (to_uint i{hr}) (64 - to_uint i{hr}))  (1 + j) by rewrite nth_sub /#.
          rewrite -H3 nth_sub /#.
qed.

lemma _x_memcpy_u8u8_64_32_post (o : W8.t Array64.t) (x : W8.t Array32.t) :
  phoare [M(Syscall)._x_memcpy_u8u8_64_32 :
    arg.`1 = o /\
    arg.`2 = x 
    ==> 
    to_list res = (to_list x) ++ sub o 32 32
  ] = 1%r by  conseq _x_memcpy_u8u8_64_32_ll (_x_memcpy_u8u8_64_32_p o x).

(** ----------------- nbytes copy ------------------ **)

lemma nbytes_copy_64_32 (o : W8.t Array64.t, _in : W8.t Array32.t)  : 
    hoare[
      M(Syscall).__nbytes_copy_offset_64_32 :
      arg = (o, W64.zero, _in, W64.zero) 
      ==> 
      sub res 0  32 = to_list _in /\
      sub res 32 32 = sub o 32 32 
    ].
proof.
proc => /=.
while (
  #{/~out = o}pre /\
  0 <= i <= 32 /\
  (forall (k : int), 0 <= k < i => out.[to_uint offset_out + k] = in_0.[to_uint offset_in + k]) /\
  (forall (k : int), 0 <= k < 32 => out.[32 + k] = o.[32 + k])
); last first.
    + auto => /> *.
      split => [/# | i????].
      have ->: i = 32 by smt(). 
      move => H0 H1.
      split.
         * apply (eq_from_nth witness); first by rewrite size_to_list size_sub.
           rewrite size_sub // => j?.
           by rewrite nth_sub // get_to_list H0.
         * apply (eq_from_nth witness); first by rewrite !size_sub.
           rewrite size_sub // => j?.
           by rewrite !nth_sub // H1.
auto => /> &hr ?? H0 H1 ?.
split => [/# |].
split => k??.
    + rewrite get_setE 1:#smt:(@W64 pow2_64).
      case (i{hr} = k) => H2; last first.
         * rewrite ifF; [ rewrite of_uintK |] => /#.
         * rewrite ifT; first by rewrite of_uintK /#.
           rewrite of_uintK H2 /#.
    + rewrite get_setE 1:#smt:(@W64 pow2_64).
      rewrite ifF; first by rewrite of_uintK /= /#.
      by apply H1.   
qed.

      
lemma nbytes_copy_64_32_ll : islossless M(Syscall).__nbytes_copy_offset_64_32
    by proc; while (true) (32 - i); auto => /> /#.

lemma nbytes_copy_64_32_p (o : W8.t Array64.t, _in : W8.t Array32.t)  : 
    phoare[
      M(Syscall).__nbytes_copy_offset_64_32 :
      arg = (o, W64.zero, _in, W64.zero) 
      ==> 
      sub res 0  32 = to_list _in /\
      sub res 32 32 = sub o 32 32 
    ] = 1%r
        by conseq nbytes_copy_64_32_ll (nbytes_copy_64_32 o _in).

(* ================================================================================= *)

require import Array131.

lemma nbytes_copy_131_32 (o : W8.t Array131.t, _in : W8.t Array32.t)  : 
    hoare[
      M(Syscall).__nbytes_copy_offset_131_32 :
      arg = (o, (W64.of_int 67), _in, W64.zero) 
      ==> 
      sub res 67 32 = to_list _in /\
      sub res 0 67 = sub o 0 67 /\ 
      sub res 99 32 = sub o 99 32 
    ].
proof.
proc => /=.
while (
  #{/~out = o}pre /\
  0 <= i <= 32 /\
  (forall (k : int), 0 <= k < i => out.[67 + k] = in_0.[k]) /\
  sub out 0 67 = sub o 0 67 /\ 
  sub out 99 32 = sub o 99 32 
); last first.
    + auto => />; split => [/# | i out???].
      rewrite (: i = 32) 1:/# => H0 H1 H2.
      apply (eq_from_nth witness); first by rewrite size_to_list size_sub.
      rewrite size_sub // => j?.
      rewrite nth_sub // H0 // get_to_list.

auto => /> &hr ??? H0  H1*; split => [/# |].
do split.
    + move => k??.
      rewrite get_setE; [rewrite of_uintK /# |].
      case (k = i{hr}) => [-> | ?].
          * rewrite ifT; rewrite of_uintK /#.
          * rewrite ifF; [rewrite of_uintK /# | smt()]. 
    + apply (eq_from_nth witness); first by rewrite !size_sub.
      rewrite size_sub // => j?.
      rewrite nth_sub //.
      rewrite get_setE; [rewrite of_uintK /# |].
      rewrite ifF; [rewrite of_uintK /# |].
      have ->: out{hr}.[0 + j] = nth witness (sub out{hr} 0 67) j by rewrite nth_sub.
      congr; apply H0.     
    + apply (eq_from_nth witness); first by rewrite !size_sub.
      rewrite size_sub // => j?.
      rewrite nth_sub //.
      rewrite get_setE; [rewrite of_uintK /# |].
      rewrite ifF; [rewrite of_uintK /# |].
      have ->: out{hr}.[99 + j] = nth witness (sub out{hr} 99 32) j by rewrite nth_sub.
      congr; apply H1.
qed.
      
lemma nbytes_copy_131_32_ll : islossless M(Syscall).__nbytes_copy_offset_131_32
    by proc; while (true) (32 - i); auto => /> /#.

lemma nbytes_copy_131_32_p (o : W8.t Array131.t, _in : W8.t Array32.t)  : 
    phoare[
      M(Syscall).__nbytes_copy_offset_131_32 :
      arg = (o, W64.of_int 67, _in, W64.zero) 
      ==> 
      sub res 67 32 = to_list _in /\
      sub res 0 67 = sub o 0 67 /\ 
      sub res 99 32 = sub o 99 32 
    ] = 1%r
        by conseq nbytes_copy_131_32_ll (nbytes_copy_131_32 o _in).
 
 (* ================================================================================= *)

lemma neg_lt (a b : int) : ! (a < b) => b <= a by smt().

lemma memcpy_ptr_touches (mem : global_mem_t) (out offset _bytes : W64.t) :
    hoare [
      M(Syscall)._x__memcpy_u8pu8p :
      arg.`1 = out /\
      arg.`2 = offset /\
      arg.`5 = _bytes /\

      0 <= to_uint _bytes /\
      to_uint out + to_uint offset < W64.modulus
      ==>
      touches Glob.mem mem (to_uint (out + offset)) (to_uint _bytes)
    ].
proof.
proc => /=.
inline.
sp.

while (
  #{/~out_offset1 = out_offset0}{/in_offset1 = in_offset0}pre /\ 
  0 <= to_uint i <= to_uint bytes1 /\
  touches Glob.mem mem (to_uint (out + offset)) (to_uint i)
); last first.
     - auto => /> &hr *; do split.
         * rewrite /touches; admit.
         * move => ??; rewrite ultE /= /#.

auto => /> &hr ??.
admit.




qed.

lemma memcpy_ptr_touches_p mem (out offset len : W64.t) :
    phoare [
      M(Syscall)._x__memcpy_u8pu8p :
      arg.`1 = out /\
      arg.`2 = offset /\
      arg.`5 = bytes
      ==>
      touches Glob.mem mem (to_uint (out + offset)) (to_uint len)
    ] = 1%r.
proof.
admit.
qed.


lemma _memcpy_u8u8_3_3_post (_in : W8.t Array3.t):
    hoare [
      M(Syscall).__memcpy_u8u8_3_3 : arg.`2 = _in 
        ==> res = _in].
proof.
proc => /=.
while (#pre /\ 0 <= to_uint i <= 3 /\ forall (k : int), 0 <= k < to_uint i => out.[k] = in_0.[k]).
  + auto => /> &hr ?? H *.
    do split => [|?|k*].
      - rewrite to_uintD /#.
      - rewrite to_uintD; smt(@W64 pow2_64).
      - rewrite get_setE 1:#smt:(@W64).
        case (k = to_uint i{hr}) => [/# | ?].
        by apply H; smt(@W64).
  + auto => /> &hr *.
    split => [/# | i out].
    rewrite ultE of_uintK /= => ???.
    have ->: to_uint i = 3 by smt().
    by rewrite tP.
qed.

lemma _memcpy_u8u8_3_3_post_p (_in : W8.t Array3.t):
    phoare [
      M(Syscall).__memcpy_u8u8_3_3 : arg.`2 = _in 
        ==> res = _in] = 1%r.
proof.
proc => /=.
while (#pre /\ 0 <= to_uint i <= 3 /\ forall (k : int), 0 <= k < to_uint i => out.[k] = in_0.[k]) (3 - to_uint i).
  + auto => /> &hr ?? H *.
    do split => [|?|k*|].
      - rewrite to_uintD /#.
      - rewrite to_uintD; smt(@W64 pow2_64).
      - rewrite get_setE 1:#smt:(@W64).
        case (k = to_uint i{hr}) => [/# | ?].
        by apply H; smt(@W64).
      - rewrite to_uintD /#.
  + auto => /> &hr *.
    split => [/# | i out].
    split. 
      - move => ????.
        rewrite ultE of_uintK /#.
      - rewrite ultE of_uintK /= => ???.
        have ->: to_uint i = 3 by smt().
        by rewrite tP.
qed.

require import Array352.

lemma memcpy_u8u8_3_352_32_post (o : W8.t Array352.t, input : W8.t Array32.t, offset : W64.t) :
  phoare [
    M(Syscall).__memcpy_u8u8_3_352_32 :
    arg =(o, input, offset, 32) /\
    0 <= to_uint offset <= 352-32 
    ==>
    (forall (k : int), 0 <= k < to_uint offset => res.[k] = o.[k]) /\
    (forall (k : int), 0 <= k < 32 => res.[to_uint offset + k] = input.[k]) /\
    (forall (k : int), to_uint offset + 32 <= k < 352 => res.[k] = o.[k])
  ] = 1%r.
proof.
admit.
qed.

(*
proc => /=.
sp 1.
while (
  #pre /\
  0 <= i <= 32 /\
  (forall (k : int), 0 <= k < i => out.[to_uint out_offset + k] = in_0.[k])
)
(32 - i); last first.
  + auto => /> *; split => [/# | j].
    split => [/# | ???].
    have ->: j = 32 by smt().
    smt().
  + auto => /> &hr *; do split; 2,3,5: by smt().
      * admit.
      * move => k??.
        rewrite get_setE 1:#smt:(@W64 pow2_64).
        case (k = i{hr}) => [-> | ?].
           - rewrite ifT // to_uintD_small of_uintK // /#.
           - rewrite ifF => [| /#].
             rewrite to_uintD_small of_uintK /#.
qed.
*)

lemma memcpy_u8u8_2_64_352_post (o : W8.t Array64.t) (_in : W8.t Array352.t) (off : W64.t):
    phoare [
       M(Syscall).__memcpy_u8u8_2_64_352 :
       arg = (o, _in, off, W64.of_int 64)       
       ==>
       to_list res.`1 = sub _in (to_uint off) 64
       ] = 1%r.
proof.
proc => /=.

admit.
qed.

