pragma Goals : printall.

require import AllCore IntDiv.

(* Lemmas about how the address is changed by each function in the Jasmin implementation *)
(* Thash_f = RandHash => Handled in Correctness Hash *)

require import Parameters XMSS_IMPL.
require import Address.

require import Array8.

from Jasmin require import JModel.

lemma set_key_and_mask_comp (a : adrs) (v0 v1 : int) :
    set_key_and_mask (set_key_and_mask a v0) v1 = set_key_and_mask a v1.
proof.
rewrite /set_key_and_mask tP => j?.
case (j = 7) => [-> | /#].
by rewrite get_setE //. 
qed.

lemma addr_prop_thash_h (a : adrs) :
    hoare [M(Syscall).__thash_f : arg.`3 = a ==> res.`2 = set_key_and_mask a 1].
proof.
proc.
seq 10 : (addr = a); first by do 3! (auto; call (: true) => //); auto.
seq 1 : (addr = set_key_and_mask a 1); first by inline; auto => />.
call (: true) => //.
while (#pre); auto => />.
by call (: true).
qed.

lemma addr_prop_gen_chain (a : adrs) (_start_ _steps_ : W32.t) :
    hoare [
      M(Syscall).__gen_chain_inplace : 
      arg.`2 = _start_ /\
      arg.`3 = _steps_ /\
      arg.`5 = a /\
      0 <= to_uint _start_ <= XMSS_WOTS_W - 1/\
      0 <= to_uint _steps_ <= XMSS_WOTS_W - 1 /\
      0 <= to_uint (_start_ + _steps_) <= XMSS_WOTS_W - 1  
      ==>  
      res.`2 = (set_key_and_mask (set_hash_addr a (to_uint (_start_ + _steps_) - 1)) 1)
    ].
proof.
proc.  
while (
  0 <= to_uint start <= 15 /\
  0 <= to_uint steps <= 15 /\
  0 <= to_uint (start + steps) <= 15 /\
  t = start + steps /\
  0 <= to_uint i <= to_uint t /\
  addr = (set_key_and_mask (set_hash_addr a (to_uint i - 1)) 1)
).
    + auto.
      inline M(Syscall).__thash_f_ M(Syscall)._thash_f.
      auto.
      ecall (addr_prop_thash_h addr). 
      inline *; auto => /> &hr H0 H1 H2 H3 H4 H5 H6 H7 H8 ? ->. 
      do split. 
          + rewrite to_uintD /#. 
          + smt(@W32 pow2_32).
          + rewrite !set_key_and_mask_comp /set_key_and_mask /set_hash_addr tP => j?.
            case (j = 0); first by smt(@Array8).
            case (j = 1); first by smt(@Array8).
            case (j = 2); first by smt(@Array8).
            case (j = 3); first by smt(@Array8).
            case (j = 4); first by smt(@Array8).
            case (j = 5); first by smt(@Array8).
            case (j = 6).
              + move => ? _ _ _ _ _ _. 
                rewrite get_setE // ifF 1:/# get_setE // ifT 1:/# get_setE // ifF 1:/# get_setE // ifT //.
                by rewrite to_uintD_small 1:#smt:(@W64) of_uintK /=.  
            (* At this point, j=7 *)
            move => ???????. 
            have ->: j = 7 by smt(). 
            rewrite get_setE // ifT // get_setE // ifT //.
    + auto => />.
      rewrite /XMSS_WOTS_W /= => H0 H1 H2 H3 H4 H5; do split. 
          + smt(@W32 pow2_32).
          + admit. (* Sem informacao sobre a??? *)
      move => i. 
      rewrite ultE => H6 H7 H8 H9 H10 H11. 
      do congr. 
      smt(@W32 pow2_32).
qed.


lemma addr_prop_expand_seed (a : adrs) :
    hoare [
        M(Syscall).__expand_seed : 
        arg.`4 = a 
        ==> 
        res.`2 = set_hash_addr (set_key_and_mask (set_chain_addr a (XMSS_WOTS_LEN) ) 0) 0
    ].
proof.
proc.
seq 5 : (addr = set_key_and_mask (set_hash_addr a 0) 0); first by inline; auto.
seq 2 : #pre; first by auto => />; call (: true).
while (
  0 <= i <= 67 /\
  addr = set_chain_addr (set_key_and_mask (set_hash_addr a 0) 0) i
).
    + inline M(Syscall).__set_chain_addr.
      do (auto; call (: true) => //). 
      auto => /> &hr *; split => [/# |]. 
      rewrite /set_chain_addr /set_key_and_mask /set_hash_addr tP => j?.
      rewrite get_setE //.
      case (j = 0); first by smt(@Array8).
      case (j = 1); first by smt(@Array8).
      case (j = 2); first by smt(@Array8).
      case (j = 3); first by smt(@Array8).
      case (j = 4); first by smt(@Array8).
      case (j = 5) => [-> _ _ _ _ _ /> |]. 
          + admit.
      case (j = 6); first by smt(@Array8).
      smt(@Array8).     
auto => />; split.
    * admit.
move => j???.
have ->: j = 67 by smt(). 
rewrite /XMSS_WOTS_LEN /=.
rewrite /set_chain_addr /set_hash_addr /set_key_and_mask tP => i?.
      case (i = 0); first by smt(@Array8).
      case (i = 1); first by smt(@Array8).
      case (i = 2); first by smt(@Array8).
      case (i = 3); first by smt(@Array8).
      case (i = 4); first by smt(@Array8).
      case (i = 5) => [-> |].
         + move => *; by rewrite get_setE.
      case (i = 6) => [-> |]; first by auto => />.
      move => ???????. 
      have ->: i = 7 by smt(). 
      move => *; auto => />. 
qed.
