pragma Goals : printall.

require import AllCore List RealExp IntDiv.
from Jasmin require import JModel.
require import Params Notation Parameters Address Primitives Wots.

require import XMSS_IMPL XMSS_IMPL_PP Generic.

require import Utils.

require import Array2 Array3 Array8 Array32 Array67 Array2144.

lemma add_sub (a b c : int) :
    a + b - c = a + b + (-c) by smt().

(** CSUM **)
lemma csum_correct (msg : W32.t Array67.t) : 
    w = XMSS_WOTS_W /\ len1 = XMSS_WOTS_LEN1 =>
    equiv [Mp(Syscall).__csum ~ WOTS.checksum :
           forall (k : int), 0 <= k < 67 => ( 0 <= to_uint msg.[k] <= (w-1) ) /\ 
           arg{1} = msg /\ arg{2} = map W32.to_uint (to_list msg) ==>
           to_uint res{1} = res{2} ].
proof.
rewrite /XMSS_WOTS_W /XMSS_WOTS_LEN1 ; move => [ w_val len1_val ].
proc.
swap {1} 1 1.
while (
  #pre /\
  to_uint csum{1} = checksum{2} /\
  i{2} = to_uint i{1} /\ 
  0 <= to_uint i{1} <= 64 /\
  0 <= to_uint csum{1} <= len1 * (w - 1) * 2^8 
  (* 0 <= to_uint msg_base_w{1}.[to_uint i{1}] <= w - 1 /\ *)
  (* nth witness m{2} i{2} = to_uint msg_base_w{1}.[to_uint i{1}] *)                   
) ; auto => />.
- move => &1 &2 H0 H1 H2 H3 H4 H5 H6;
  rewrite w_val len1_val //= in H4 ;
  rewrite len1_val //= in H6 ;  do split.
  + pose j := to_uint i{1}. pose l := (to_list msg_base_w{1}).
    rewrite -get_to_list to_uintD //=.
    have E : (to_uint (csum{1} + (of_int 15)%W32)) = to_uint csum{1} + 15. 
    rewrite to_uintD //= /#.
    rewrite w_val //=. 
    have E2 : to_uint (csum{1} + (of_int 15)%W32) = to_uint csum{1} + 15 by smt(@W64).
    rewrite E2. admit.
  + rewrite to_uintD_small ; smt(@W64).
  + smt(@W64).
  + smt(@W64).
  + admit. 
  + admit.
  + rewrite ultE of_uintK ; smt(@W64).
  + rewrite ultE of_uintK ; smt(@W64). 
- progress ; [ by rewrite len1_val w_val | by rewrite len1_val ].
qed.

(** Base-W **)
lemma base_w_correctness_67 (o : W32.t Array67.t, i : W8.t Array32.t) :
    w = XMSS_WOTS_W /\ floor (log2 w%r) = XMSS_WOTS_LOG_W =>
    equiv [M(Syscall).__base_w_67_32 ~ BaseW.base_w :
      arg{1} = (o, i) /\ arg{2} = (to_list i, 67) ==>
      res{2} = map W32.to_uint (to_list res{1})].
proof.
rewrite /XMSS_WOTS_W /XMSS_WOTS_LOG_W ; move => [w_val logw_val].
proc.
admit.
qed.

(* Gen Chain *)
require import Utils.

lemma memcpy_32_t (_out : W8.t Array32.t) (_in_ptr : W64.t) :
    hoare [Mp(Syscall)._memcpy_u8u8p_32 : 
    valid_ptr _in_ptr (W64.of_int 32) /\ arg = (_out, _in_ptr) ==> 
      res  = Array32.init (fun (i:int) => loadW8 Glob.mem ((W64.to_uint _in_ptr) + i))].
proof.
proc ; inline*.
sp ; wp.
while (
  0 <= to_uint i <= 32 /\
  forall (k : int), 0 <= k < to_uint i => out0.[k] = loadW8 Glob.mem (to_uint (in_ptr0 + i))
) ; auto => />.
progress.
    + rewrite to_uintD_small // /#.
    + smt(@W64).
    + admit.
- progress.
    + smt.
    + admit. (* Apply H4 *)
qed.

lemma gen_chain_correctness(_out : W8.t Array32.t, _in_ptr : W64.t, _start : W32.t,
                         _steps : W32.t, seed : W8.t Array32.t, _address : W32.t Array8.t) :
n = XMSS_N => 
equiv [ Mp(Syscall).__gen_chain ~ Chain.chain :
 valid_ptr _in_ptr (W64.of_int 32) /\ 
={Glob.mem} /\ 
arg{1} = (_out, _in_ptr, _start, _steps, seed, _address) /\ 
arg{2} = (mkseq (fun (i:int) => loadW8 Glob.mem{2} ((W64.to_uint _in_ptr) + i)) n, to_uint _start, to_uint _steps, to_list seed, _address)
==> res{2} = to_list res{1}.`1].
proof.
rewrite /XMSS_N ; move => n_val.
proc.
admit.
qed.
