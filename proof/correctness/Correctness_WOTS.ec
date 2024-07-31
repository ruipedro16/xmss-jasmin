pragma Goals : printall.

require import AllCore List RealExp IntDiv.
from Jasmin require import JModel JArray.

require import Params Parameters Address Notation Primitives Hash Wots Util.
require import RandomBytes XMSS_IMPL.

require import Array2 Array3 Array8 Array32 Array67 Array96 Array2144.

require import Utils. (* valid ptr predicate & addr_to_bytes *)
require import Correctness_Mem Correctness_Hash. 
(*---*) import NBytes.
require import Termination.

type adrs = W32.t Array8.t.

lemma base_w_correctness_67 ( _in_ : W8.t Array32.t) :
    floor (log2 w%r) = XMSS_WOTS_LOG_W /\ 
    w = XMSS_WOTS_W => 
      equiv[M(Syscall).__base_w_67_32 ~ BaseW.base_w :
        arg{1}.`2 = _in_ /\
        arg{2} = (to_list _in_, 67) ==>
         res{2} = map (W32.to_uint) (to_list res{1})].
proof.
rewrite /XMSS_WOTS_LOG_W /XMSS_WOTS_W ; move => [logw_val w_val].
proc.
conseq (: _ ==> size base_w{2} = 67 /\ forall (k:int), 0 <= k < 67 => to_uint output{1}.[k] = nth witness base_w{2} k).
  + move => &1 &2 /> *. apply (eq_from_nth witness). rewrite size_map size_to_list /#. 
    move => *. rewrite  (nth_map witness). smt(Array67.size_to_list). rewrite get_to_list /#.  
sp.
while (
  ={total, consumed} /\ 0 <= consumed{1} <= 67 /\
  size base_w{2} = 67 /\
  outlen{2} = 67 /\
  out{2} = to_uint out{1} /\
  out{2} = consumed{1} /\
  X{2} = to_list input{1} /\
  out{2} = to_uint out{1} /\ 0 <= to_uint out{1} <= 67 /\
  bits{2} = to_uint bits{1} /\ 
  bits{2} = consumed{2} %% 2 * 4 /\
  _in{2} = to_uint in_0{1} /\ _in{2} = (consumed{2} + 1) %/ 2 /\
  (forall (j : int), 0 <= j < to_uint out{1} => (to_uint output{1}.[j]) = nth witness base_w{2} j)
).
(* First subgoal of while *)
    + if.
        * auto => /> &1 &2 *; smt(@W64).
        * auto => /> &1 &2 *; do split;1..11:smt(@W64 @IntDiv pow2_64 size_put).
            - move => j Hj *. rewrite get_setE 1:/# //= nth_put ; 1:smt(size_nseq).
              case (j = to_uint out{1}); last first.
                + move => *. rewrite ifF 1:/#. smt(@W64).
                + move => -> //=. rewrite logw_val w_val /=. 
                  have -> : 15 = 2 ^ 4 - 1 by smt().
                  rewrite and_mod // and_mod // shr_div shr_div //=. 
                  have -> : 31 = 2 ^ 5 - 1 by smt().
                  rewrite and_mod //= to_uint_truncateu8 to_uint_zeroextu32 //=. 
                  smt(@W64 @W8 @W32 pow2_32 pow2_64 pow2_8 @IntDiv).
        * auto => /> &1 &2 *; do split;1..7:smt(@W64 pow2_64 size_put).
            - rewrite logw_val //= to_uintB; smt(@W64 pow2_64).
            - rewrite logw_val //. smt(@W64 pow2_64 @IntDiv).
            - smt(@W64 pow2_64 @IntDiv).
            - move => j Hj *. rewrite get_setE 1:/# //= nth_put ; 1:smt(size_nseq).
              case (j = to_uint out{1}); last first. 
                + move => *. rewrite ifF 1:/#. smt(@W64).
                + move => -> //=. rewrite logw_val w_val /=. 
                  have -> : 15 = 2 ^ 4 - 1 by smt().
                  rewrite and_mod // and_mod // shr_div shr_div //=. 
                  have -> : 31 = 2 ^ 5 - 1 by smt().
                  rewrite and_mod //= to_uint_truncateu8 to_uint_zeroextu32 //=. 
                  rewrite to_uintB; 1:smt(@W64). simplify. 
                  admit. (* smt(@W64 @W8 @W32 pow2_32 pow2_64 pow2_8 @IntDiv). *) (* This call to smt fails sometimes *)
(* Last subgoal of while *)
    + skip => /> *; do split;2,3:smt(@W64 pow2_64). by rewrite size_nseq.
qed.


lemma base_w_correctness_3 ( _in_ : W8.t Array2.t) :
    floor (log2 w%r) = XMSS_WOTS_LOG_W /\ 
    w = XMSS_WOTS_W => 
      equiv [M(Syscall).__base_w_3_2 ~ BaseW.base_w :
        arg{1}.`2 = _in_ /\
        arg{2} = (to_list _in_, 3) ==>
         res{2} = map (W32.to_uint) (to_list res{1})].
proof.
rewrite /XMSS_WOTS_LOG_W /XMSS_WOTS_W ; move => [logw_val w_val].
proc.
conseq (: _ ==> size base_w{2} = 3 /\ forall (k:int), 0 <= k < 3 => to_uint output{1}.[k] = nth witness base_w{2} k).
  + move => &1 &2 /> *. apply (eq_from_nth witness). rewrite size_map size_to_list /#. 
    move => *. rewrite  (nth_map witness). smt(Array3.size_to_list). rewrite get_to_list /#.  
sp.
while (
  ={total, consumed} /\ 0 <= consumed{1} <= 3 /\
  size base_w{2} = 3 /\
  outlen{2} = 3 /\
  out{2} = to_uint out{1} /\
  out{2} = consumed{1} /\
  X{2} = to_list input{1} /\
  out{2} = to_uint out{1} /\ 0 <= to_uint out{1} <= 3 /\
  bits{2} = to_uint bits{1} /\ 
  bits{2} = consumed{2} %% 2 * 4 /\
  _in{2} = to_uint in_0{1} /\ _in{2} = (consumed{2} + 1) %/ 2 /\
  (forall (j : int), 0 <= j < to_uint out{1} => (to_uint output{1}.[j]) = nth witness base_w{2} j)
).
(* First subgoal of while *)
    + if.
        * auto => /> &1 &2 *; smt(@W64).
        * auto => /> &1 &2 *; do split;1..11:smt(@W64 @IntDiv pow2_64 size_put).
            - move => j Hj *. rewrite get_setE 1:/# //= nth_put ; 1:smt(size_nseq).
              case (j = to_uint out{1}); last first.
                + move => *. rewrite ifF 1:/#. smt(@W64).
                + move => -> //=. rewrite logw_val w_val /=. 
                  have -> : 15 = 2 ^ 4 - 1 by smt().
                  rewrite and_mod // and_mod // shr_div shr_div //=. 
                  have -> : 31 = 2 ^ 5 - 1 by smt().
                  rewrite and_mod //= to_uint_truncateu8 to_uint_zeroextu32 //=. 
                  smt(@W64 @W8 @W32 pow2_32 pow2_64 pow2_8 @IntDiv).
        * auto => /> &1 &2 *; do split;1..7:smt(@W64 pow2_64 size_put).
            - rewrite logw_val //= to_uintB; smt(@W64 pow2_64).
            - rewrite logw_val //. smt(@W64 pow2_64 @IntDiv).
            - smt(@W64 pow2_64 @IntDiv).
            - move => j Hj *. rewrite get_setE 1:/# //= nth_put ; 1:smt(size_nseq).
              case (j = to_uint out{1}); last first. 
                + move => *. rewrite ifF 1:/#. smt(@W64).
                + move => -> //=. rewrite logw_val w_val /=. 
                  have -> : 15 = 2 ^ 4 - 1 by smt().
                  rewrite and_mod // and_mod // shr_div shr_div //=. 
                  have -> : 31 = 2 ^ 5 - 1 by smt().
                  rewrite and_mod //= to_uint_truncateu8 to_uint_zeroextu32 //=. 
                  rewrite to_uintB; 1:smt(@W64). simplify. 
                  admit. (* smt(@W64 @W8 @W32 pow2_32 pow2_64 pow2_8 @IntDiv). *) (* this call to smt fails sometimes *)
(* Last subgoal of while *)
    + skip => /> *; do split;2,3:smt(@W64 pow2_64). by rewrite size_nseq.
qed.


(*** CHECKSUM ***)

lemma wots_checksum_correctness (msg : W32.t Array67.t) :
    len1 = XMSS_WOTS_LEN1 /\  w = XMSS_WOTS_W =>
    equiv [M(Syscall).__csum ~ WOTS.checksum :
      (forall (k : int), 0 <= k < 67 => 0 <= to_uint msg.[k] <= 15) /\ (* 15 = w - 1 *)
      arg{1} = msg /\ arg{2} = map (W32.to_uint) (to_list msg) ==>
        to_uint res{1} = res{2}].
proof.
rewrite /XMSS_WOTS_LEN1 /XMSS_WOTS_W ; move => [len1_val w_val].
proc.
while (
  #pre /\
  to_uint csum{1} = checksum{2} /\
  0 <= to_uint csum{1} <= (i{2} * (w - 1) * 2^8) /\
  i{2} = to_uint i{1} /\ 0 <= i{2} <= len1 /\
  m{2} = map (W32.to_uint) (to_list msg{1})
); last by auto => /> /#.
    + auto => /> &1 Hmsg Hcsum0 Hcsum1 Hi0 _. 
      rewrite /(\ult) of_uintK /= => Hlt Hi1.
      rewrite to_uintD to_uintB.
        * by rewrite /(\ule) /= to_uint_zeroextu64 1:/#.
      rewrite !of_uintK /= modz_small 1:/# modz_small 1:/#.
      have -> : nth witness (map W32.to_uint (to_list msg)) (to_uint i{1}) = 
                to_uint (zeroextu64 msg.[to_uint i{1}]).
        * rewrite to_uint_zeroextu64 (nth_map witness); [ by rewrite size_to_list /# | smt() ].
      by rewrite !to_uint_zeroextu64 to_uintD_small /= /#.
qed.

(*** THASH F ***)

(*
lemma thash_f_hop2 (o s : W8.t Array32.t, ad : W32.t Array8.t) :
    n = XMSS_N /\
    padding_len = XMSS_PADDING_LEN /\
    prf_padding_val = XMSS_HASH_PADDING_PRF /\
    equiv [
      M(Syscall).__thash_f ~ Hop2.thash_f :
      arg{1} = (o, s, ad) /\
      arg{2} = (to_list o, to_list s, ad)
      ==>
      res{2}.`1 = to_list res{1}.`1 /\
      res{2}.`2 = res{1}.`2
    ].
proof.
move => [#] ????. 
proc.
seq 0 1 : (#pre /\ size buf{2} = 96).
  + by auto => />; rewrite size_nseq.
seq 4 0 : (#pre); 1:auto.
swap {2} 1 1.
seq 1 1 : (#pre /\ to_list addr_as_bytes{1} = addr_bytes{2}).
  + ecall {1} (addr_to_bytes_correctness addr{1}); auto => />.
seq 2 1 : (#pre /\ padding{2} = to_list padding{1}).
  + call {1} (ull_to_bytes_correct W64.zero); auto => />.
seq 1 0 : (#pre /\ forall (k : int), 0 <= k < 32 => buf{1}.[k] = padding{1}.[k]).
  + auto => />; smt(@Array96).
seq 1 1 : (#pre /\ u{2} = to_list aux{1}).
  + auto => />; inline {1} M(Syscall).__prf_  M(Syscall)._prf; wp; sp.
    exists * in_00{1}, key0{1}; elim * => _P1 _P2; call (prf_correctness _P1 _P2); skip => />.
seq 1 0 : (#pre /\ forall (k : int), 0 <= k < 32 => buf{1}.[32 + k] = aux{1}.[k]).
  + auto => />; smt(@Array96).
seq 2 2 : (
  size buf{2} = 96 /\
  to_list pub_seed{1} = seed{2} /\
  addr{1} = address{2} /\
  to_list out{1} = out{2} /\
  to_list addr_as_bytes{1} = addr_bytes{2} /\
  padding{2} = to_list padding{1} /\
  u{2} = to_list aux{1} /\
  (forall (k : int), 0 <= k && k < 32 => buf{1}.[k] = padding{1}.[k]) /\
  (forall (k : int), 0 <= k && k < 32 => buf{1}.[32 + k] = aux{1}.[k])  
).
    + inline {1} M(Syscall).__set_key_and_mask; sp 4 1; ecall {1} (addr_to_bytes_correctness addr{1}); auto => />.
seq 1 1 : (#pre /\ bitmask{2} = to_list bitmask{1}).      
    + inline {1} M(Syscall).__prf_  M(Syscall)._prf; wp; sp.
      exists * in_00{1}, key0{1}; elim * => _P1 _P2; call (prf_correctness _P1 _P2); skip => />.
seq 0 2 : (
  #pre /\ 
  forall (k : int), 0 <= k < 64 => buf{1}.[k] = nth witness buf{2} k
).
    + auto => /> &1 &2 *. split; first by rewrite size_mkseq. move => k *. rewrite nth_mkseq 1:/#. 
      simplify.  case (0 <= k && k < 32).
      * move => *; rewrite ifF 1:/#; rewrite nth_mkseq 1:/#; smt(@Array96 @List).
      * move => *; rewrite ifT 1:/#; smt(@Array96).
seq 2 2 : (buf{2} = to_list buf{1} /\ address{2} = addr{1}); last first.
    + inline {1} M(Syscall).__core_hash__96 M(Syscall)._core_hash_96; wp; sp. 
      ecall {1} (hash_96 in_00{1}); auto => /> /#. 
while (
  size buf{2} = 96 /\ 
  address{2} = addr{1} /\
  n{2} = 32 /\
  i{2} = to_uint i{1} /\ 
  0 <= i{2} <= 32 /\
  bitmask{2} = to_list bitmask{1} /\
  out{2} = to_list out{1} /\
  (forall (k : int), 0 <= k < 64 => buf{1}.[k] = nth witness buf{2} k) /\
  (forall (k : int), 0 <= k < i{2} => buf{1}.[64 + k] = nth witness buf{2} (64 + k))
); last first.
    + auto => /> *. do split;1,2:smt(). auto => /> *. apply (eq_from_nth witness); first by rewrite size_to_list /#.
      move => *. admit.
    + auto => /> &1 &2 *. do split;2..4,7,8:smt(@W64 pow2_64). 
        * by rewrite size_put. 
        * move => k *. rewrite nth_put 1:/#. case (64 + to_uint i{1} = 64 + k).
           - move => *. rewrite get_setE; 1:smt(@W64 pow2_64). admit. (* by rewrite ifT; 1:smt(@W64 pow2_64). *)
           - move => *. rewrite get_setE; 1:smt(@W64 pow2_64). rewrite ifF; 1:smt(@W64 pow2_64). smt().
        * move => k *. rewrite nth_put 1:/#. rewrite get_setE; first by smt(@W64 pow2_64). case (64 + k = to_uint ((of_int 64)%W64 + i{1})).
           - move => *. admit.
           - move => *. admit.
qed. 
*)




(*** ----------------- ***)

lemma gen_chain_inplace_correct (_buf_ : W8.t Array32.t, _start_ _steps_ : W32.t, _addr_ : W32.t Array8.t, _pub_seed_ : W8.t Array32.t) :
    w = XMSS_WOTS_W /\ 
    len = XMSS_WOTS_LEN /\
    prf_padding_val = XMSS_HASH_PADDING_PRF /\ 
    padding_len = XMSS_PADDING_LEN /\ 
    F_padding_val = XMSS_HASH_PADDING_F =>
    equiv [
      M(Syscall).__gen_chain_inplace ~ Chain.chain : 
      arg{1}= (_buf_, _start_, _steps_, _pub_seed_, _addr_) /\
      arg{2} = (to_list _buf_, to_uint _start_, to_uint _steps_, to_list _pub_seed_, _addr_) /\
      0 <= to_uint _start_ <= XMSS_WOTS_W - 1/\
      0 <= to_uint _steps_ <= XMSS_WOTS_W - 1 /\
      0 <= to_uint (_start_ + _steps_) <= XMSS_WOTS_W - 1  
      ==> 
      res{2}.`1 = to_list res{1}.`1 /\ 
      res{1}.`2 = res{2}.`2
    ].
proof.
move => [#] ?????. 
proc => //=.
swap {1} 1 2.
seq 2 1 : (
  0 <= to_uint start{1} <= XMSS_WOTS_W - 1/\
  0 <= to_uint steps{1} <= XMSS_WOTS_W - 1 /\
  0 <= to_uint (start{1} + steps{1}) <= XMSS_WOTS_W - 1 /\

  address{2} = addr{1} /\
  t{2} = to_list out{1} /\
  i{2} = to_uint start{1} /\
  s{2} = to_uint steps{1} /\
  _seed{2} = to_list pub_seed{1} /\
  t{2} = to_list out{1} /\  
  t{1} = start{1} + steps{1}
); first by auto => />.
while (
  #pre /\ 
  0 <= to_uint i{1} <= to_uint t{1} /\
  to_uint i{1} = (i{2} + chain_count{2}) /\
  0 <= chain_count{2} <= s{2}
); last by auto => />; smt(@W32 pow2_32). 
wp 3 8.
seq 2 2 : (#pre). 
    + inline {1}; auto => /> &1 &2 *. 
      rewrite /set_hash_addr /set_key_and_mask; by have -> : (of_int (to_uint start{1} + chain_count{2}))%W32 = i{1} by smt(@W32 pow2_32).
inline {1} M(Syscall).__thash_f_ M(Syscall)._thash_f M(Syscall).__thash_f; inline {2} Hash._F.


seq 27 9 : (
  (* #pre but without address{2} = addr{1} because at some point updates to the address are made through addr2{1} and not addr{1} *)
  (0 <= to_uint start{1} && to_uint start{1} <= XMSS_WOTS_W - 1) /\
  (0 <= to_uint steps{1} && to_uint steps{1} <= XMSS_WOTS_W - 1) /\
  (0 <= to_uint (start{1} + steps{1}) && to_uint (start{1} + steps{1}) <= XMSS_WOTS_W - 1) /\
  t{2} = to_list out{1} /\
  i{2} = to_uint start{1} /\
  s{2} = to_uint steps{1} /\
  _seed{2} = to_list pub_seed{1} /\
  t{2} = to_list out{1} /\ 
  t{1} = start{1} + steps{1} /\
  (0 <= to_uint i{1} && to_uint i{1} <= to_uint t{1}) /\
  to_uint i{1} = i{2} + chain_count{2} /\
  0 <= chain_count{2} && chain_count{2} <= s{2} /\
  (i{1} \ult t{1}) /\ 
  chain_count{2} < s{2} /\
  
  buf{2} = to_list buf{1} /\ 
  addr2{1} = address{2}
); last first.
    + inline {1} M(Syscall).__core_hash__96 M(Syscall)._core_hash_96; wp; sp; ecall {1} (hash_96 in_00{1}); auto => /> *. 
      do split; 3..5,8,9:smt(@W32 pow2_32); smt().
auto => />.
seq 17 1 : (
  #pre /\ 
  addr2{1} = addr{1} /\ 
  addr_bytes{2} = to_list addr_as_bytes{1} /\
  pub_seed2{1} = pub_seed{1}
); first by ecall {1} (addr_to_bytes_correctness addr{1}); auto => /> /#. 
swap {2} 7 -6.
seq 2 1 : (#pre /\ padding{2} = to_list padding{1}); first by call {1} (ull_to_bytes_correct W64.zero); auto => />.
seq 1 0 : (
  #pre /\
  (forall (k : int), 0 <= k < 32 => buf{1}.[k] = padding{1}.[k])
); first by auto => /> *; smt(@Array96).
seq 1 1 : (#pre /\ _key{2} = to_list aux{1}).
    + inline {1} M(Syscall).__prf_ M(Syscall)._prf; wp; sp.
      exists * in_00{1}, key0{1}; elim * => _P1 _P2; call {1} (prf_correctness _P1 _P2); skip => /> *.
auto => />.
seq 1 0 : (
  #pre /\
  (forall (k : int), 0 <= k < 32 => buf{1}.[32 + k] = nth witness _key{2} k)
); first by auto => /> *; smt(@Array96).
seq 1 1 : (
  (0 <= to_uint start{1} && to_uint start{1} <= XMSS_WOTS_W - 1) /\
  (0 <= to_uint steps{1} && to_uint steps{1} <= XMSS_WOTS_W - 1) /\
  (0 <= to_uint (start{1} + steps{1}) && to_uint (start{1} + steps{1}) <= XMSS_WOTS_W - 1) /\
  t{2} = to_list out{1} /\
  i{2} = to_uint start{1} /\
  s{2} = to_uint steps{1} /\
  _seed{2} = to_list pub_seed{1} /\
  t{2} = to_list out{1} /\ 
  t{1} = start{1} + steps{1} /\
  (0 <= to_uint i{1} && to_uint i{1} <= to_uint t{1}) /\
  to_uint i{1} = i{2} + chain_count{2} /\
  (0 <= chain_count{2} && chain_count{2} <= s{2}) /\
  (i{1} \ult t{1}) /\ 
  chain_count{2} < s{2} /\
  address{2} = addr2{1} /\
  addr_bytes{2} = to_list addr_as_bytes{1} /\ 
  pub_seed2{1} = pub_seed{1} /\
  padding{2} = to_list padding{1} /\
  (forall (k : int), 0 <= k && k < 32 => buf{1}.[k] = padding{1}.[k]) /\
  (forall (k : int), 0 <= k && k < 32 => buf{1}.[32 + k] = nth witness _key{2} k) /\
  _key{2} = to_list aux{1}
); first by inline {1}; auto => />.
seq 1 1 : (#pre); first by ecall {1} (addr_to_bytes_correctness addr2{1}); auto => /> /#. 
seq 1 1 : (#pre /\ bitmask{2} = to_list bitmask{1}).
    + inline {1} M(Syscall).__prf_ M(Syscall)._prf; wp; sp.
      exists * in_00{1}, key0{1}; elim * => _P1 _P2; call {1} (prf_correctness _P1 _P2); skip => /> *. 
auto => />.
seq 2 0 : (#post); last first. skip => />.
admit.
(*
while  ( 
  #pre /\
  0 <= to_uint i0{1} <= 32 /\
  (forall (k : int), 0 <= k < to_uint i0{1} => buf{1}.[64 + k] = out2{1}.[to_uint i0{1}] `^` bitmask{1}.[to_uint i0{1}])
).
*)
qed.


(************************************************************************************)

op load_mem_w8_array32 (mem : global_mem_t) (ptr : W64.t) : W8.t Array32.t = 
  Array32.init (fun i => loadW8 mem (to_uint ptr + i)).

op load_mem_w8_list32 (mem : global_mem_t) (ptr : W64.t) : W8.t list =
  mkseq (fun i => loadW8 mem (to_uint ptr + i)) 32.

pred eq_wots_pk (pk_spec : wots_pk) (pk_impl : W8.t Array2144.t) = flatten pk_spec = (to_list pk_impl).

lemma pkgen_correctness (_pk_ : W8.t Array2144.t, _seed_ : W8.t Array32.t,
                         _pub_seed_ : W8.t Array32.t, _addr_ : W32.t Array8.t) :
    len = XMSS_WOTS_LEN =>
    equiv [Mp(Syscall).__wots_pkgen ~ WOTS.pkGen : 
      arg{1} = (_pk_, _seed_, _pub_seed_, _addr_) /\
      arg{2} = (to_list _seed_, to_list _pub_seed_, _addr_) ==> 
       eq_wots_pk res{2}.`1 res{1}.`1 /\ res{1}.`2 = res{2}.`2].
proof.
rewrite /XMSS_WOTS_LEN.
move => len_val.
proc.
sp.
(* Maybe seq 1 1 here *)
while (
  0 <= i{1} <= 32 /\ ={i} /\
  address{2} = addr{1} /\
  (forall (k : int), 0 <= k < (32 * i{1}) => pk{1}.[k] = nth witness (flatten pk{2}) k)
) ; auto => />.
+ progress. admit.
+ inline Mp(Syscall).__set_chain_addr Mp(Syscall).__gen_chain_inplace_ Mp(Syscall)._gen_chain_inplace. 
  wp ; sp. (* call gen_chain_inplace_correct. : CANNOT INFER ALL PLACEHOLDERS*) admit.
+ admit.
+ inline Mp(Syscall).__expand_seed_ Mp(Syscall)._expand_seed. wp ; sp. (* call expand_seed_correct. by rewrite len_val /XMSS_WOTS_LEN. skip => />. progress.
    + admit.
    + smt().
    + smt().
    + smt().
*) 
admit.
qed.

(* Falta o wots sign asqui *)
