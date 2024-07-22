pragma Goals : printall.

require import AllCore List RealExp IntDiv.
require import XMSS_IMPL RandomBytes.

from Jasmin require import JModel.

lemma initH_ref_ll : islossless M(Syscall).__initH_ref by proc ; auto.

lemma store_H_ref_ll : islossless M(Syscall).__store_H_ref by proc ; auto.

lemma load_H_ref_ll : islossless M(Syscall).__load_H_ref by proc ; auto.

lemma store_ref_array_ll : islossless M(Syscall).__store_ref_array
    by proc;while (0 <= i <= 8) (8 - i); auto => /#.

lemma Wt_ref_ll : islossless M(Syscall).__Wt_ref by proc ; inline ; auto.

lemma blocks_1_ref_ll : 
    phoare[M(Syscall)._blocks_1_ref : 0 <= to_uint nblocks < W64.modulus ==> true] = 1%r.       proof.
proc.
wp;sp.
while (#pre /\ 0 <= to_uint i <= to_uint nblocks) ((to_uint nblocks) - (to_uint i)); last by auto => /> * ; smt(@W64).
auto => />.
call store_H_ref_ll ; wp.
while (0 <= to_uint tr <= 64) (64 - (to_uint tr)).
    - auto => />. inline*. auto => /> * ; smt(@W64 pow2_64).
    - auto => /> *; last first.
        + admit.
        + admit.  
qed.

lemma blocks_0_ref_96_ll : islossless M(Syscall)._blocks_0_ref_96.
proof.
proc.
sp ; wp.
if; last by auto.
admit.
(*
while (64 <= to_uint inlen <= W64.max_uint ) ((to_uint inlen) - 64); first by admit.

  + skip => /> *. admit.



 last by admit.
  + auto => /> * ; wp. 
    call store_H_ref_ll ; wp.
    while (0 <= to_uint tr <= 64) (64 - (to_uint tr)); first by admit.
    wp ; call load_H_ref_ll ; wp.
    while (16 <= t <= 64) (64 - t); first by auto => /> * ; call Wt_ref_ll ; skip => /> /#.
    wp. while (0 <= t <= 16) (16 - t); first by auto => /> /#. 
auto => /> *; do split.
smt().
admit.
*)
qed.

lemma lastblocks_ref_96_ll : islossless M(Syscall).__lastblocks_ref_96.
proof.
proc.
sp;wp.
while (true) ((to_uint i) - (to_uint j)).
  + admit.
wp.
while (0 <= to_uint i <= to_uint inlen /\ 0 <= to_uint inlen <= W64.modulus) 
      ((to_uint inlen) - (to_uint i)); first by auto => /> *; smt(@W64 pow2_64). 
while (0 <= k <= 32) (32 - k); 1:auto => /> /#.
skip => /> *; progress.
smt().
smt(@W64 pow2_64).
smt(@W64 pow2_64).
smt(@W64 pow2_64).
smt(@W64 pow2_64).
search [!] (\ule).
rewrite -ultNge. admit.
rewrite -ultNge. admit.
qed.

lemma sha256_96_ll :islossless M(Syscall).__sha256_96.
proof.
proc.
call store_ref_array_ll ; wp.
call blocks_1_ref_ll ; wp.
call lastblocks_ref_96_ll ; wp.
call blocks_0_ref_96_ll ; wp.
call initH_ref_ll ; auto.
qed.
