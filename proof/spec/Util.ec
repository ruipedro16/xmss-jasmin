pragma Goals : printall.

require import AllCore List Distr RealExp IntDiv.
require import BitEncoding.
(*---*) import BitChunking.

from Jasmin require import JModel.

require import Types.
(*---*) import NBytes.

op nbytexor(a b : nbytes) : nbytes = 
    map (fun (ab : W8.t * W8.t) => ab.`1 `^` ab.`2) (zip a b).

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

