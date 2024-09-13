pragma Goals : printall.

require import AllCore List Distr RealExp IntDiv.
require import BitEncoding.
(*---*) import BitChunking.

from Jasmin require import JModel.

require import XMSS_MT_Types Array8.

op BytesToBits (bytes : W8.t list) : bool list = flatten (map W8.w2bits bytes).
op BitsToBytes (bits : bool list) : W8.t list = map W8.bits2w (chunk W8.size bits).
op W64ToBytes (w : W64.t, outlen : int) : W8.t list. (* = BitsToBytes (W64.w2bits w). *)

op addr_to_bytes (a : W32.t Array8.t) : W8.t list = 
  let addr_bits : bool list = flatten (mkseq (fun (i : int) => W32.w2bits a.[i]) 8) in
  BitsToBytes addr_bits.


pred is_even (x : int) = x %% 2 = 0.

op _ceil_2 (a : int) : int = 
  if is_even a 
  then to_uint (W64.of_int a `>>` W8.one) 
  else to_uint (W64.of_int a `>>` W8.one) + 1.

op _floor_2 (a : int) : int = 
  to_uint (W64.of_int a `>>` W8.one).

op nbytexor(a b : nbytes) : nbytes = 
    map (fun (ab : W8.t * W8.t) => ab.`1 `^` ab.`2) (zip a b).

lemma shr_1 (x : W64.t) :
    to_uint (x `>>` W8.one) = to_uint x %/ 2
        by rewrite shr_div (: (to_uint W8.one %% 64) = 1) 1:#smt:(@W64) //=. 

lemma size_nbyte_xor (a b : nbytes) :
    size a = size b =>
      size (nbytexor a b) = size a
        by rewrite /nbytexor size_map size_zip /#. 

(******************************************************************************)

(* gets the n most significant bits *)
op msb (x : W8.t list) (n : int) : W8.t list = take n x. 

(* gets the n most significant bits of x *)
(* n is at most 32 *)
op msb_w32 (x : W32.t) (n : int) : bool list = take n (w2bits x).

(* Returns the n most significant bits of x as a W32.t *)
op msb_w32_int (x : W32.t) (n : int) : W32.t = 
  let bits : bool list = take n (w2bits x) in
  (W32.bits2w bits).

op lsb_w32_int (x : W32.t) (n : int) : W32.t =
   let bits : bool list =  w2bits x in
   let lsbits : bool list =  drop ((size bits) - n) bits in
   W32.bits2w lsbits.

(******************************************************************************)

(* Stack operations *)
op push (x : 'a list) (a : 'a) : 'a list = rcons x a. 

op remove_last (x : 'a list) : 'a list = 
with x = [] => []
with x = h::t => if t = [] then [] else remove_last t.

op pop (x : 'a list) : 'a list * 'a = 
    let last_elem = last witness x in
    let new_list = remove_last x in
    (new_list, last_elem).

(******************************************************************************)

module Util = {
  proc w64_to_bytes (in_0 : W64.t, outlen : int) = {
    var r : W8.t list <- nseq outlen W8.zero;
    var i : int;
    var t : W8.t;

    i <- outlen - 1;

    while (0 <= i) {
      t <- (truncateu8 in_0);            (* Get the lowest 8 bits *)
      r <- put r i t;
      in_0 <- (in_0 `>>` (W8.of_int 8)); (* Shift right by 8 bits *)
      i <- i - 1;                        (* Move to the next byte *)
    }

    return r;
  } 
}.

lemma w64_to_bytes_ll : 
    phoare [Util.w64_to_bytes : 0 <= outlen ==> true] = 1%r
        by proc; while (#pre) (i + 1); auto => /> /#.

