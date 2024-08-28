pragma Goals : printall.

require import AllCore List RealExp IntDiv.
from Jasmin require import JModel JArray.

require import Types Params Parameters Address Notation Hash Primitives Wots XMSS_MT_PRF.
require import XMSS_IMPL.
require import Repr. 
require import Array8 Array32 Array64 Array2144.

(*---*) import NBytes.

require import Correctness_Mem Correctness_Hash.
require import Utils.

require import BitEncoding.
(*---*) import BitChunking.

(*** L Tree ***)

lemma ltree_correct (_pk : W8.t Array2144.t, _pub_seed : W8.t Array32.t, _addr : W32.t Array8.t) : 
    len = XMSS_WOTS_LEN /\ 
    n = XMSS_N =>
    equiv [
      M(Syscall).__l_tree ~ LTree.ltree :
      arg{1}.`2 = _pk /\
      arg{1}.`3 = _pub_seed /\
      arg{1}.`4 = _addr /\
      arg{2} = (EncodeWotsPk _pk, _addr, to_list _pub_seed)
      ==>
      to_list res{1}.`1 = res{2}.`1 /\ (* wots pk *)
      res{1}.`3 = res{2}.`2 (* address *)
    ].
proof.
move => [#] *.
proc. 
auto => />.
seq 3 1 : (#pre); first by auto. 
seq 1 1 : (#pre /\ _len{2} = to_uint l{1} /\ _len{2} = 67);  first by auto.
seq 2 1 : (
  addr{1} = address{2} /\
  pk{2} = EncodeWotsPk wots_pk{1} /\
  _seed{2} = to_list pub_seed{1} /\
  _len{2} = to_uint l{1} /\
  _len{2} = 67
); first by inline {1}; auto. 
seq 1 1 : (
  addr{1} = address{2} /\ 
  (forall (k : int), 0 <= k < 32 => wots_pk{1}.[k] = nth witness (nth witness pk{2} 0) k) /\
  size pk{2} = len /\
  forall (t : W8.t list), t \in pk{2} => size t = n
); last first.
    + ecall {1} (_x_memcpy_u8u8_post tmp{1}).
      auto => /> &1 &2 ???.
      apply (eq_from_nth witness); [ rewrite (size_nth pk{2} 32 0);1,2:smt(); by rewrite size_to_list | smt(@Array32) ].
(*-------------------------------------------------------------------------------------------------------------------------------------------*)
while (
  0 <= _len{2} <= 67 /\
  _len{2} = to_uint l{1} /\
  _seed{2} = to_list pub_seed{1} /\
  size pk{2} = len /\
  addr{1} = address{2} /\ 
  (forall (k : int), 0 <= k < 32 => wots_pk{1}.[k] = nth witness (nth witness pk{2} 0) k) /\
  (forall (t : W8.t list), t \in (pk{2}) => size t = n)
); last by admit.

    + seq 2 0 : (#pre /\ to_uint parent_nodes{1} = floor (len%r / 2%r)). 
      * auto => /> &1 &2 *. 
        have ->: truncateu8 (W256.one `&` (of_int 63)%W256) = W8.one by admit.
        rewrite shr_div.
        have ->: 2 ^ (to_uint W8.one %% 64) = 2 by smt(@W8).
        admit.
    
     

(* ------------------------- *)

    + skip => /> &1 *. do split.

smt().
smt().
rewrite size_enc_wots_pk /#.
move => k ? ?. 
    + admit. (* rewrite -nth_flatten. rewrite size_enc_wots_pk /#. rewrite (size_nth (EncodeWotsPk wots_pk{1}) 32 0); smt(size_enc_wots_pk ssize_enc_wots_pk). *)      
smt(ssize_enc_wots_pk).
smt(@W64 pow2_64).
smt(@W64 pow2_64).
qed.

(*** Treehash ***)

(******* exported functions ********)
