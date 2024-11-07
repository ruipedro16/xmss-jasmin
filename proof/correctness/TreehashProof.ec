pragma Goals : printall.

require import AllCore List RealExp IntDiv Distr DList.
from Jasmin require import JModel JArray.

require import BitEncoding.
(*---*) import BitChunking.

require import StdBigop. 
(*---*) import Bigint.

require import Params XMSS_MT_Params Types XMSS_MT_Types Address Hash BaseW WOTS LTree XMSS_MT_TreeHash XMSS_MT_PRF.
require import XMSS_IMPL Parameters.
require import Repr2 Utils2.

require import Array4 Array8 Array11 Array32 Array64 Array131 Array320 Array352 Array2144 Array2464.

require import Correctness_Address.
require import Correctness_WOTS.
require import Correctness_Mem.
require import Correctness_Conditions.
require import LTReeProof.

require import WArray32.

require import TreehashHop.

lemma treehash_correct ( _sk_seed _pub_seed : W8.t Array32.t, _s _t:W32.t, _addr:W32.t Array8.t): 
    n = XMSS_N /\
    d = XMSS_D /\
    h = XMSS_FULL_HEIGHT /\
    h %/d = XMSS_TREE_HEIGHT /\
    w = XMSS_WOTS_W /\
    len = XMSS_WOTS_LEN /\
    n = XMSS_N /\
    prf_padding_val = XMSS_HASH_PADDING_PRF /\
    prf_kg_padding_val = XMSS_HASH_PADDING_PRF_KEYGEN /\
    padding_len = XMSS_PADDING_LEN /\
    F_padding_val = XMSS_HASH_PADDING_F =>
    equiv [
      M(Syscall).__treehash ~ TreeHashHop.treehash :

      arg{1}.`2 = _sk_seed /\
      arg{1}.`3 = _pub_seed /\
      arg{1}.`4 = _s /\
      arg{1}.`5 = _t /\
      arg{1}.`6 = _addr /\
      
      arg{2}.`1 = NBytes.insubd (to_list _pub_seed) /\
      arg{2}.`2 = NBytes.insubd (to_list _sk_seed) /\
      arg{2}.`3 = to_uint _s /\
      arg{2}.`4 = to_uint _t /\
      arg{2}.`5 = _addr /\

      0 <= to_uint _t <= h /\
      0 <= to_uint _s <= to_uint _t
      ==>
      to_list res{1} = val res{2}
    ]. 
proof.
rewrite /XMSS_N /XMSS_D /XMSS_TREE_HEIGHT /XMSS_FULL_HEIGHT /XMSS_D /= => [#] n_val d_val h_val tree_height *.
proc => /=.

seq 7 0 : #pre; first by auto.
seq 4 2 : (
  #pre /\
  offset{1} = W64.zero /\
  ots_addr{1} = subtree_addr{1} /\
  ltree_addr{1} = subtree_addr{1} /\
  node_addr{1} = subtree_addr{1} /\
  size stack{2} = h %/ d + 1 /\
  size heights{2} = h %/ d
).
    + auto => /> *; do split;4,5: by smt(size_nseq).
         * rewrite tP => j*.
           rewrite initiE //= get32E pack4E wordP => i?.
           rewrite initiE //= initiE 1:/# /= /init64 initiE 1:/# /= /copy_64 initiE 1:/# /=.
           rewrite  get64E pack8E bits8iE 1:/# initiE 1:/# /= initiE 1:/# //= /init32 initiE 1:/# /= bits8iE /#.
         * rewrite tP => j*.
           rewrite initiE //= get32E pack4E wordP => i?.
           rewrite initiE //= initiE 1:/# /= /init64 initiE 1:/# /= /copy_64 initiE 1:/# /=.
           rewrite  get64E pack8E bits8iE 1:/# initiE 1:/# /= initiE 1:/# //= /init32 initiE 1:/# /= bits8iE /#.
         * rewrite tP => j*.
           rewrite initiE //= get32E pack4E wordP => i?.
           rewrite initiE //= initiE 1:/# /= /init64 initiE 1:/# /= /copy_64 initiE 1:/# /=.
           rewrite  get64E pack8E bits8iE 1:/# initiE 1:/# /= initiE 1:/# //= /init32 initiE 1:/# /= bits8iE /#.

seq 3 3 : (
  #{/~ots_addr{1} = subtree_addr{1}}
   {/~ltree_addr{1} = subtree_addr{1}}
   {/~node_addr{1} = subtree_addr{1}}pre /\
   ots_addr{1} = ots_address{2} /\
   ltree_addr{1} = ltree_address{2} /\
   node_addr{1} = node_address{2}
); first by inline {1}; auto.

seq 1 1 : (#pre /\ to_uint offset{1} = offset{2}); first by auto.

swap {1} 1 2.

seq 2 0 : (#pre /\ to_uint upper_bound{1} = 2^t{2}).
    + auto => /> &2 *.
      rewrite (: 31 = 2^5 - 1) 1:/# and_mod // shl_shlw 1:#smt:(@W32) of_uintK to_uint_shl 1:/# /=.
      have ->: to_uint _t %% 32 %% 4294967296 = to_uint _t by smt(modz_small).
      have E: 0 <= 2 ^ h < 4294967296 by rewrite h_val /#.
      smt(@IntDiv @RealExp).

seq 2 2 : (sub _stack{1} 0 n = val (nth witness stack{2} 0)); last first.
    + while {1}
    (#pre /\
     0 <= j{1} <= 32 /\ 
     node{2} = nth witness stack{2} 0 /\
     forall (k : int), 0 <= k < j{1} => root{1}.[k] = nth witness (val (nth witness stack{2} 0)) k) 
    (32 - j{1}); last first.
        * auto => /> &1 &2 ?; split => [/# | j?]; split => [/# |???].
          have ->: j = 32 by smt().
          move => H.
          apply (eq_from_nth witness); first by rewrite valP n_val size_to_list.
          rewrite size_to_list => ??.
          by rewrite get_to_list H.
        * auto => /> &hr H0 ?? H1 *; do split; 1,2,4: by smt().
          move => k??.
          rewrite get_setE 1:/#.
          case (k = j{hr}) => [-> | ?]; last by apply H1 => /#. 
          rewrite -get_to_list -H0.
          by rewrite nth_sub 1:/# get_to_list.

while (
  t{2} = to_uint target_height{1} /\ 
  0 <= t{2} <= h /\ (* Target height *)

  s{2} = to_uint start_index{1} /\ 
  0 <= s{2} <= h /\ (* start index  *) 

  offset{2} = to_uint offset{1} /\  

  (i{2} <> 0 => 0 < offset{2}) /\

  0 <= offset{2} < size stack{2} /\

  size stack{2} = h %/ d + 1 /\ 
  size heights{2} = h %/ d /\

  0 <= i{2} <= 2^t{2} /\
  i{2} <= to_uint target_height{1} /\
  to_uint i{1} = i{2} /\

  to_uint upper_bound{1} = 2^t{2} /\

  sk_seed{2} = (insubd (to_list sk_seed{1}))%NBytes /\
  pub_seed{2} = (insubd (to_list pub_seed{1}))%NBytes /\ 

  map W32.to_uint (sub heights{1} 0 offset{2}) = sub_list heights{2} 0 offset{2} /\
  sub _stack{1} 0 (n * offset{2}) = sub_list (nbytes_flatten stack{2}) 0 (n * offset{2}) /\
  
  sub ots_addr{1} 0 5 = sub ots_address{2} 0 5 /\
  ltree_addr{1} = ltree_address{2}
); last by admit.

seq 2 0 : (#pre /\ to_uint t32{1} = s{2} + i{2}).
    + auto => /> *; rewrite to_uintD /#.

swap {1} 2 -1.
  
seq 1 1 : #pre.
    + inline {1}; auto => /> &1 &2 ???????????????H1??H.
      rewrite /set_ots_addr.
      apply (eq_from_nth witness); first by rewrite !size_sub.
      rewrite size_sub // => i?.
      rewrite !nth_sub // get_setE //=.
      case (i = 4) => [-> |?]. 
          * by rewrite get_setE // ifT // -H to_uintK.
      rewrite get_setE // ifF //.
      have ->: ots_addr{1}.[i] = nth witness (sub ots_addr{1} 0 5) i by rewrite nth_sub.
      by rewrite H1 nth_sub.

seq 1 0 : (
    #{/~ltree_addr{1} = ltree_address{2}}pre /\ 
    ltree_addr{1} = set_ltree_addr ltree_address{2} (s{2} + i{2})
).
    + inline {1}; auto => /> &1 &2 ??????????????????H.
      rewrite /set_ltree_addr tP => i?.
      rewrite get_setE //.
      case (i = 4) => [-> |?]; rewrite -H; first by smt(to_uintK).
      by rewrite get_setE // ifF 1:/#.

inline {1} M(Syscall).__gen_leaf_wots_ M(Syscall)._gen_leaf_wots M(Syscall).__gen_leaf_wots.             

sp 22 0.

seq 1 1 : (
  #{/~ots_addr2{1} = ots_addr1{1}}
   {/~_00{1} = witness}
   {/~pk{1} = witness}pre /\
  pk{1} = DecodeWotsPk pk{2} /\
  sub ots_addr2{1} 0 5 = sub ots_addr1{1} 0 5
).
    + exists * sk_seed2{1}, pub_seed2{1}, ots_addr2{1}, ots_address{2}; elim * => P0 P1 P2 P3.
      call (pkgen_results P0 P1 P2 P3) => [/# |].
      skip => /> &1 &2 ??????????????? H1 ???.  
      do split.
        * move => k??.
          have ->: P2.[k] = nth witness (sub P2 0 5) k by rewrite nth_sub.
          rewrite H1. (* H1 is the hypothesis H1: sub P2 0 5 = sub P3 0 5 *)
          by rewrite nth_sub.
        * move => H0 rL rR H2 H3.
          apply (eq_from_nth witness); first by rewrite !size_sub.
          rewrite size_sub // => i?.
          by rewrite nth_sub // H3 // nth_sub. (* H3 is the hypothesis H3: forall (k : int), 0 <= k && k < 5 => rL.`2.[k] = P2.[k] *)

seq 0 1 : (
    #{/~ ltree_addr{1} = set_ltree_addr ltree_address{2} (s{2} + i{2})}pre /\
    ltree_addr{1} = ltree_address{2} 
); first by auto.

seq 0 0 : (#pre /\ ltree_addr2{1} = ltree_address{2}); first by auto.

seq 1 1 : (
  #{/~ltree_addr2{1} = ltree_addr1{1}}
   {/~ltree_addr2{1} = ltree_address{2}}pre /\
  to_list leaf1{1} = val node{2} /\
  sub ltree_addr{1} 0 5 = sub ltree_address{2} 0 5 /\
  ltree_addr2{1}.[5] = W32.of_int 7 /\
  ltree_addr2{1}.[6] = W32.zero /\
  ltree_addr2{1}.[7] = W32.of_int 2 
).  
    + exists * pk{1}, ltree_addr2{1}, pub_seed2{1}.
      elim * => P0 P1 P2.
      call (ltree_correct P0 P2 P1) => [/# |].
      skip => /> &1 &2 ????????????????????.
      split.
         * apply enc_dec_wots_pk => /#.
         * move => H0 rL rR H1 H2 H3 H4 H5.
           admit.

seq 0 3 : (#pre /\ ltree_addr2{1} = ltree_address{2}).
    + auto => /> &1 &2 ????????????????????????.
      rewrite /set_key_and_mask /set_tree_index /set_tree_height; do split.
          - admit.
          * apply (eq_from_nth witness); first by rewrite !size_sub.
            rewrite size_sub // => i?.
            rewrite !nth_sub //=. 
            by do 3! (rewrite get_setE // ifF 1:/#).
          * rewrite tP => i?.
            rewrite !get_setE //.
            case (i = 5) => [-> |?].
               - by rewrite ifF.
            case (i = 6) => [-> |?].
               - by rewrite ifF //.
            case (i = 7) => [-> /#| ?].
            have ?: 0 <= i < 5 by smt().
            have ->: ltree_addr2{1}.[i] = nth witness (sub ltree_addr2{1} 0 5) i by rewrite nth_sub. (* Falta uma hipotese sobre o sub ltree 0 5 *)
            admit.

seq 6 0 : false.

seq 2 0 : (#pre /\ to_uint t64{1} = 32 * offset{2}).
    + admit.


 
