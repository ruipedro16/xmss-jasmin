pragma Goals : printall.

require import AllCore List RealExp IntDiv.

from Jasmin require import JModel JArray.

require import Params Hash BaseW WOTS. 

require import XMSS_IMPL Parameters.

require import Array2 Array3 Array8 Array32 Array64 Array67 Array96 Array2144.

require import Correctness_Bytes Correctness_Mem Correctness_Address Correctness_Hash.
require import Termination.

require import BitEncoding.
(*---*) import BitChunking.

require import StdBigop. 
(*---*) import Bigint.

lemma nbyte_xor_val (a b : nbytes): 
    val (nbytexor a b) = bytexor (val a) (val b).
proof.
rewrite /nbytexor NBytes.insubdK //= /P /bytexor size_map size_zip.
rewrite (: (size (val a)) = n) 1:#smt:(NBytes.valP).
rewrite (: (size (val b)) = n) 1:#smt:(NBytes.valP).
smt(ge0_n).
qed.

lemma zip_fst (a b : W8.t list) (i : int):
  0 <= i < min (size a) (size b) =>
    (nth witness (zip a b) i).`1 = nth witness a i 
      by smt(@List).

lemma zip_snd (a b : W8.t list) (i : int):
  0 <= i < min (size a) (size b) =>
    (nth witness (zip a b) i).`2 = nth witness b i 
      by smt(@List).

lemma base_w_correctness_64 ( _in_ : W8.t Array32.t) :
    floor (log2 w%r) = XMSS_WOTS_LOG_W /\ 
    w = XMSS_WOTS_W => 
      equiv[M(Syscall).__base_w_64_32 ~ BaseW.base_w :
        arg{1}.`2 = _in_ /\
        arg{2} = (to_list _in_, 64) ==>
         res{2} = map (W32.to_uint) (to_list res{1})].
proof.
rewrite /XMSS_WOTS_LOG_W /XMSS_WOTS_W ; move => [logw_val w_val].
proc.
conseq (: _ ==> size base_w{2} = 64 /\ forall (k:int), 0 <= k < 64 => to_uint output{1}.[k] = nth witness base_w{2} k).
  + move => &1 &2 /> *. 
    apply (eq_from_nth witness); [rewrite size_map size_to_list /# |]. 
    move => *. 
    rewrite (nth_map witness) #smt:(Array64.size_to_list). 
sp.
while (
  ={total, consumed} /\ 0 <= consumed{1} <= 64 /\
  size base_w{2} = 64 /\
  outlen{2} = 64 /\
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
        * admit. (* auto => /> &1 &2 *; do split;1..11:smt(@W64 @IntDiv pow2_64 size_put).
            - move => j Hj *. rewrite get_setE 1:/# //= nth_put ; 1:smt(size_nseq).
              case (j = to_uint out{1}); last first.
                + move => *. rewrite ifF 1:/#. smt(@W64).
                + move => -> //=. rewrite logw_val w_val /=.  
                  have -> : 15 = 2 ^ 4 - 1 by smt().
                  rewrite and_mod // and_mod // shr_div shr_div //=. 
                  have -> : 31 = 2 ^ 5 - 1 by smt().
                  rewrite and_mod //= to_uint_truncateu8 to_uint_zeroextu32 //=. 
                  admit. (* smt(@W64 @W8 @W32 pow2_32 pow2_64 pow2_8 @IntDiv). *)
            *)
        * auto => /> &1 &2 *; do split;1..7:smt(@W64 pow2_64 size_put).
            - rewrite logw_val //= to_uintB #smt:(@W64 pow2_64).
            - rewrite logw_val // #smt:(@W64 pow2_64 @IntDiv).
            - smt(@W64 pow2_64 @IntDiv).
            - move => j Hj *. rewrite get_setE 1:/# //= nth_put 1:#smt:(size_nseq).
              case (j = to_uint out{1}); last first. 
                + move => *; rewrite ifF 1:/# #smt:(@W64).
                + move => -> //=. rewrite logw_val w_val /=. 
                  have -> : 15 = 2 ^ 4 - 1 by smt().
                  rewrite and_mod // and_mod // shr_div shr_div //=. 
                  have -> : 31 = 2 ^ 5 - 1 by smt().
                  rewrite and_mod //= to_uint_truncateu8 to_uint_zeroextu32 //=. 
                  rewrite to_uintB 1:#smt:(@W64) //=. 
                  admit. (* smt(@W64 @W8 @W32 pow2_32 pow2_64 pow2_8 @IntDiv). *) (* This call to smt fails sometimes *)
(* Last subgoal of while *)
    + skip => /> *; do split;2,3:smt(@W64 pow2_64). by rewrite size_nseq.
qed.

lemma base_w_results_64 ( _in_ : W8.t Array32.t) :
    floor (log2 w%r) = XMSS_WOTS_LOG_W /\ 
    w = XMSS_WOTS_W => 
    equiv[
      M(Syscall).__base_w_64_32 ~ BaseW.base_w :
      arg{1}.`2 = _in_ /\
      arg{2} = (to_list _in_, 64) 
      ==>
      res{2} = map (W32.to_uint) (to_list res{1}) /\
      forall (k : int), 0 <= k < 64 => 0 <= to_uint res{1}.[k] < w
    ].
proof.
admit. (* correctness + bounds *)
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
  + move => &1 &2 /> *. 
    apply (eq_from_nth witness); [rewrite size_map size_to_list /# |]. 
    move => *.  
    rewrite (nth_map witness) #smt:(Array3.size_to_list).
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
            - move => j Hj *. rewrite get_setE 1:/# //= nth_put 1:#smt:(size_nseq).
              case (j = to_uint out{1}); last first.
                + move => *. rewrite ifF 1:/# #smt:(@W64).
                + move => -> //=. rewrite logw_val w_val /=. 
                  have -> : 15 = 2 ^ 4 - 1 by smt().
                  rewrite and_mod // and_mod // shr_div shr_div //=. 
                  have -> : 31 = 2 ^ 5 - 1 by smt().
                  rewrite and_mod //= to_uint_truncateu8 to_uint_zeroextu32 //=. 
                  admit. (* smt(@W64 @W8 @W32 pow2_32 pow2_64 pow2_8 @IntDiv). *)
        * auto => /> &1 &2 *; do split;1..7:smt(@W64 pow2_64 size_put).
            - rewrite logw_val //= to_uintB #smt:(@W64 pow2_64).
            - rewrite logw_val // #smt:(@W64 pow2_64 @IntDiv).
            - smt(@W64 pow2_64 @IntDiv).
            - move => j Hj *. rewrite get_setE 1:/# //= nth_put 1:#smt:(size_nseq).
              case (j = to_uint out{1}); last first. 
                + move => *. rewrite ifF 1:/# #smt:(@W64).
                + move => -> //=. rewrite logw_val w_val /=. 
                  have -> : 15 = 2 ^ 4 - 1 by smt().
                  rewrite and_mod // and_mod // shr_div shr_div //=. 
                  have -> : 31 = 2 ^ 5 - 1 by smt().
                  rewrite and_mod //= to_uint_truncateu8 to_uint_zeroextu32 //=. 
                  rewrite to_uintB 1:#smt:(@W64) //=. 
                  admit. (* smt(@W64 @W8 @W32 pow2_32 pow2_64 pow2_8 @IntDiv). *) (* this call to smt fails sometimes *)
(* Last subgoal of while *)
    + skip => /> *; do split;2,3:smt(@W64 pow2_64). by rewrite size_nseq.
qed.

lemma base_w_results_3 ( _in_ : W8.t Array2.t) :
    floor (log2 w%r) = XMSS_WOTS_LOG_W /\ 
    w = XMSS_WOTS_W => 
    equiv[
      M(Syscall).__base_w_3_2 ~ BaseW.base_w :
      arg{1}.`2 = _in_ /\
      arg{2} = (to_list _in_, 3) 
      ==>
      res{2} = map (W32.to_uint) (to_list res{1}) /\
        forall (x : int), x \in res{2} => 0 <= x < w
    ].
proof.
move => [#] ??. 
admit.
qed.

lemma wots_checksum_correctness (msg : W32.t Array64.t) :
    len1 = XMSS_WOTS_LEN1 /\  w = XMSS_WOTS_W =>
    equiv [M(Syscall).__csum ~ WOTS.checksum :
      (forall (k : int), 0 <= k < 64 => 0 <= to_uint msg.[k] <= 15) /\ (* 15 = w - 1 *)
      arg{1} = msg /\ arg{2} = map (W32.to_uint) (to_list msg) ==>
        to_uint res{1} = res{2}].
proof.
rewrite /XMSS_WOTS_LEN1 /XMSS_WOTS_W => [#] len1_val w_val.
proc.
while (
  #pre /\
  to_uint csum{1} = checksum{2} /\
  0 <= to_uint csum{1} <= (i{2} * (w - 1) * 2^8) /\
  i{2} = to_uint i{1} /\ 
  0 <= i{2} <= len1 /\
  m{2} = map (W32.to_uint) (to_list msg{1})
); last by auto => /> /#.
    + auto => /> &1 Hmsg Hcsum0 Hcsum1 Hi0 _. 
      rewrite /(\ult) of_uintK /= => Hlt Hi1.
      rewrite to_uintD to_uintB.
        * by rewrite /(\ule) /= to_uint_zeroextu64 1:/#.
      rewrite !of_uintK /= modz_small 1:/# modz_small 1:/#.
      have -> : nth witness (map W32.to_uint (to_list msg)) (to_uint i{1}) = 
                to_uint (zeroextu64 msg.[to_uint i{1}]).
        * rewrite to_uint_zeroextu64 (nth_map witness) //= size_to_list /#. 
      by rewrite !to_uint_zeroextu64 to_uintD_small /= /#.
qed.

lemma wots_checksum_results (msg : W32.t Array64.t) :
    len1 = XMSS_WOTS_LEN1 /\  w = XMSS_WOTS_W =>
    equiv [
      M(Syscall).__csum ~ WOTS.checksum :
      (forall (k : int), 0 <= k < 64 => 0 <= to_uint msg.[k] <= 15) /\ (* 15 = w - 1 *)
      arg{1} = msg /\ arg{2} = map (W32.to_uint) (to_list msg) 
      ==>
      to_uint res{1} = res{2} /\
        0 <= res{2} <= len1 * (w - 1) 
    ].
proof.
admit.
qed.

lemma gen_chain_inplace_correct (_buf_ : W8.t Array32.t, _start_ _steps_ : W32.t, _addr_ : W32.t Array8.t, _pub_seed_ : W8.t Array32.t) :
    n = XMSS_N /\
    w = XMSS_WOTS_W /\ 
    len = XMSS_WOTS_LEN /\
    prf_padding_val = XMSS_HASH_PADDING_PRF /\ 
    padding_len = XMSS_PADDING_LEN /\ 
    F_padding_val = XMSS_HASH_PADDING_F =>
    equiv [
      M(Syscall).__gen_chain_inplace ~ Chain.chain : 
      arg{1}= (_buf_, _start_, _steps_, _pub_seed_, _addr_) /\
      arg{2} = (NBytes.insubd (to_list _buf_), to_uint _start_, to_uint _steps_, NBytes.insubd (to_list _pub_seed_), _addr_) /\
      0 <= to_uint _start_ <= XMSS_WOTS_W - 1/\
      0 <= to_uint _steps_ <= XMSS_WOTS_W - 1 /\
      0 <= to_uint (_start_ + _steps_) <= XMSS_WOTS_W - 1  
      ==> 
      val res{2}.`1 = to_list res{1}.`1 /\ 
      res{1}.`2 = res{2}.`2
    ].
proof. 
rewrite /XMSS_N.
move => [#] nval ?????. 
proc => //=.
swap {1} 1 2.
seq 2 1 : ( 
  0 <= to_uint start{1} <= XMSS_WOTS_W - 1/\
  0 <= to_uint steps{1} <= XMSS_WOTS_W - 1 /\
  0 <= to_uint (start{1} + steps{1}) <= XMSS_WOTS_W - 1 /\

  address{2} = addr{1} /\
  val t{2} = to_list out{1} /\
  i{2} = to_uint start{1} /\
  s{2} = to_uint steps{1} /\
  val _seed{2} = to_list pub_seed{1} /\
  val t{2} = to_list out{1} /\  
  t{1} = start{1} + steps{1}
); first by auto => /> *; do split; by rewrite NBytes.insubdK /P // size_to_list nval.
while (
  #pre /\ 
  0 <= to_uint i{1} <= to_uint t{1} /\
  to_uint i{1} = (i{2} + chain_count{2}) /\
  0 <= chain_count{2} <= s{2}
); last by auto => />; smt(@W32 pow2_32). 
wp 3 8.
seq 2 2 : (#pre). 
    + inline {1}; auto => /> &1 &2 *. 
      rewrite /set_hash_addr /set_key_and_mask.
      by have -> : (of_int (to_uint start{1} + chain_count{2}))%W32 = i{1} by smt(@W32 pow2_32). 
inline {1} M(Syscall).__thash_f_ M(Syscall)._thash_f M(Syscall).__thash_f.
inline {2} Hash._F.
seq 27 9 : (
  (0 <= to_uint start{1} && to_uint start{1} <= XMSS_WOTS_W - 1) /\
  (0 <= to_uint steps{1} && to_uint steps{1} <= XMSS_WOTS_W - 1) /\
  (0 <= to_uint (start{1} + steps{1}) && to_uint (start{1} + steps{1}) <= XMSS_WOTS_W - 1) /\
  val t{2} = to_list out{1} /\
  i{2} = to_uint start{1} /\
  s{2} = to_uint steps{1} /\
  val _seed{2} = to_list pub_seed{1} /\
  val t{2} = to_list out{1} /\ 
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
seq 17 1 : (
  #pre /\ 
  addr2{1} = addr{1} /\ 
  addr_bytes{2} = to_list addr_as_bytes{1} /\
  pub_seed2{1} = pub_seed{1} /\
  out2{1} = out{1}
); first by ecall {1} (addr_to_bytes_correctness addr{1}); auto => /> /#. 
swap {2} 7 -6.
seq 2 1 : (#pre /\ padding{2} = to_list padding{1}); first by call {1} (ull_to_bytes_32_correct W64.zero); auto => /> /#.

seq 1 0 : (
  #pre /\
  (forall (k : int), 0 <= k < 32 => buf{1}.[k] = padding{1}.[k])
); first by auto => /> *; smt(@Array96).

seq 1 1 : (
  #pre /\ 
  val _key{2} = to_list aux{1}
).
    + inline {1} M(Syscall).__prf_ M(Syscall)._prf; wp; sp.
      exists * in_00{1}, key0{1}; elim * => _P1 _P2.
      call {1} (prf_correctness _P1 _P2) => [/# |]. 
      skip => /> &1 &2 ??????? H *.
      rewrite -H #smt:(@NBytes).
seq 1 0 : (
  #pre /\
  (forall (k : int), 0 <= k < 32 => buf{1}.[32 + k] = nth witness (val _key{2}) k)
).
    + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16.
      split => k??; rewrite initiE 1:/# => />.
         * rewrite ifF 1:/#.
           apply H15 => //.
         * by rewrite ifT 1:/# H16 get_to_list.
seq 1 1 : (
  (0 <= to_uint start{1} && to_uint start{1} <= XMSS_WOTS_W - 1) /\
  (0 <= to_uint steps{1} && to_uint steps{1} <= XMSS_WOTS_W - 1) /\
  (0 <= to_uint (start{1} + steps{1}) && to_uint (start{1} + steps{1}) <= XMSS_WOTS_W - 1) /\
  val t{2} = to_list out{1} /\
  i{2} = to_uint start{1} /\
  s{2} = to_uint steps{1} /\
  val _seed{2} = to_list pub_seed{1} /\
  val t{2} = to_list out{1} /\ 
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
  (forall (k : int), 0 <= k && k < 32 => buf{1}.[32 + k] = aux{1}.[k]) /\
  val _key{2} = to_list aux{1} /\
  out2{1} = out{1}
).
    + inline {1}.
      auto => /> &1 &2 ??????????????? H0 H1 H2.
      move => k??. 
      by rewrite H2 //= H1 get_to_list.
seq 1 1 : (#pre); first by ecall {1} (addr_to_bytes_correctness addr2{1}); auto => /> /#. 
seq 1 1 : (#pre /\ val bitmask{2} = to_list bitmask{1}).
    + inline {1} M(Syscall).__prf_ M(Syscall)._prf; wp; sp.
      exists * in_00{1}, key0{1}; elim * => _P1 _P2; call {1} (prf_correctness _P1 _P2) => [/# |].
      skip => /> &1 &2 ???????H*. 
      rewrite -H #smt:(@NBytes). 
while{1}  ( 
  #pre /\
  0 <= to_uint i0{1} <= 32 /\
  (forall (k : int), 0 <= k < to_uint i0{1} => buf{1}.[64 + k] = out{1}.[k] `^` bitmask{1}.[k])
) (32 - to_uint i0{1}). 
    + auto => /> &hr *; do split;3,4,6:smt(@W64 pow2_64).
        * move => *. rewrite get_setE 1:#smt:(@W64) ifF 1:#smt:(@W64 pow2_64) #smt:(@Array96).
        * move => *. rewrite get_setE 1:#smt:(@W64) ifF 1:#smt:(@W64 pow2_64) #smt:(@Array96).
        * move => k *. rewrite get_setE 1:#smt:(@W64). 
          case (64 + k = to_uint ((of_int 64)%W64 + i0{hr})); [move => ?; do congr |]; smt(@W64 pow2_64).
    + auto => /> &1 &2. 
      move => H0 H1 H2 H3 H4 H5 H6 H7 H8 H9.
      move => H10 H11 H12 H13 H14 H15 H16 H17 H18. 
      split; first by smt(@Array96). 
      move => bufL i0 *; split; first by smt(@W64 pow2_64). 
      move => ?????. 
      have ->: to_uint i0 = 32 by smt(@W64 pow2_64).
      move => ?. 
      apply (eq_from_nth witness).     
           * rewrite !size_cat !size_to_list.
             have ->: size (val _key{2}) = 32 by smt(NBytes.valP).
             by have ->: size (val (nbytexor t{2} bitmask{2})) = 32 by smt(size_map size_zip NBytes.valP).
      have ->:  size (to_list padding{1} ++ val _key{2} ++ val (nbytexor t{2} bitmask{2})) = 96.
           * rewrite !size_cat !size_to_list.
             have ->: size (val _key{2}) = 32 by smt(NBytes.valP).
             by have ->: size (val (nbytexor t{2} bitmask{2})) = 32 by smt(size_map size_zip NBytes.valP).
      move => j Hj.  
      case (0 <= j < 32) => *.
           * rewrite nth_cat. 
             have ->: size (to_list padding{1} ++ val _key{2}) = 64.
               - by rewrite size_cat size_to_list (: size (val _key{2}) = 32) 1:#smt:(NBytes.valP).
             rewrite ifT 1:/# get_to_list nth_cat size_to_list ifT 1:/# get_to_list /#.
      case (32 <= j < 64) => *.
           * rewrite nth_cat. 
             have ->: size (to_list padding{1} ++ val _key{2}) = 64.
               - by rewrite size_cat size_to_list (: size (val _key{2}) = 32) 1:#smt:(NBytes.valP). 
             rewrite ifT 1:/# get_to_list nth_cat size_to_list ifF 1:/# H17 get_to_list /#.
      rewrite nth_cat. 
      have ->: size (to_list padding{1} ++ val _key{2}) = 64.
           * by rewrite size_cat size_to_list (: size (val _key{2}) = 32) 1:#smt:(NBytes.valP). 
      rewrite ifF 1:/# get_to_list nbyte_xor_val H18 H6 /bytexor.
      rewrite (nth_map witness); [rewrite size_zip !size_to_list /# |].
      auto => />. 
      rewrite zip_fst; [rewrite !size_to_list /# |]. 
      rewrite zip_snd; [rewrite !size_to_list /# |]. 
      rewrite !get_to_list /#. 
qed.

(*** Expand Seed : Done ***)

lemma expand_seed_correct (_in_seed _pub_seed : W8.t Array32.t, _addr : W32.t Array8.t) :
    len = XMSS_WOTS_LEN /\ 
    n = XMSS_N /\ 
    prf_padding_val = XMSS_HASH_PADDING_PRF /\
    prf_kg_padding_val = XMSS_HASH_PADDING_PRF_KEYGEN /\
    padding_len = XMSS_PADDING_LEN =>
    equiv [M(Syscall).__expand_seed ~ WOTS.pseudorandom_genSK :
      arg{1}.`2 = _in_seed /\ 
      arg{1}.`3 = _pub_seed /\
      arg{1}.`4 = _addr /\
      arg{2} = (to_list _in_seed, to_list _pub_seed, _addr) ==>
      res{1}.`1 = DecodeWotsSk res{2}.`1 /\ 
      res{1}.`2 = res{2}.`2].
proof.
move => [#] len_val n_val ???.
proc; auto => />.
conseq (: _ ==> addr{1} = address{2} /\ (forall (k : int), 0 <= k < 2144 => outseeds{1}.[k] = nth witness (flatten sk{2}) k)).
  + auto => /> *; rewrite /DecodeWotsSk /of_list tP; smt(@Array2144).
seq 5 3 : (
  sk_seed{2} = to_list inseed{1} /\
  seed{2} = to_list pub_seed{1} /\
  address{2} = addr{1} /\
  size sk{2} = len /\ 
  (forall (k : int), 0 <= k < size sk{2} => size (nth witness sk{2} k)  = n) /\
  size (flatten sk{2}) = len * n 
); first by inline{1}; auto => />; smt(@List).
seq 1 0 : (#pre /\ aux{1} = pub_seed{1}); first by ecall {1} (_x_memcpy_u8u8_post pub_seed{1}); auto => />.
seq 1 0 : (#pre /\ forall (k : int), 0 <= k < 32 => buf{1}.[k] = pub_seed{1}.[k]); first by auto => />; smt(@Array64).
while (
  len{2} = 67 /\
  size sk{2} = len /\ 
  ={i} /\ 0 <= i{2} <= 67 /\ 
  address{2} = addr{1} /\
  sk_seed{2} = to_list inseed{1} /\
  seed{2} = to_list pub_seed{1} /\
  (forall (k : int), 0 <= k < 32 => buf{1}.[k] = pub_seed{1}.[k]) /\
  (forall (k : int), 0 <= k < 32 * i{2} => outseeds{1}.[k] = nth witness (flatten sk{2}) k) /\
  (forall (k : int), 0 <= k < size sk{2} => size (nth witness sk{2} k)  = n)
); last by auto => /> /#.  
seq 2 1 : (#pre); first by inline {1}; auto => />.
seq 1 1 : (#pre /\ addr_bytes{2} = to_list addr_bytes{1}); first by ecall {1} (addr_to_bytes_correctness addr{1}); auto => /> /#. 
seq 1 0 : (#pre /\ (forall (k : int), 0 <= k < 32 => buf{1}.[32 + k] = addr_bytes{1}.[k])); first by auto => /> ; smt(@Array64).
seq 0 0 : (#pre /\ to_list buf{1} = (seed{2} ++ addr_bytes{2})).
    + skip => /> &1 &2 *. apply (eq_from_nth witness); [ by rewrite size_cat !size_to_list | move => *; congr; rewrite /to_list /mkseq -iotaredE => /> /# ].
seq 2 1 : (#pre /\ sk_i{2} = to_list ith_seed{1}).
    + inline {1} M(Syscall).__prf_keygen_ M(Syscall)._prf_keygen; wp; sp.
      exists * in_00{1}, key0{1}; elim * => _P1 _P2; call {1} (prf_keygen_correctness _P1 _P2); auto => /> *. 
      rewrite /to_list /mkseq -iotaredE => /> /#. 
auto => /> &1 &2  ? sizeSK ??? H0 H *. do split; 2,3,6,7:smt(); [ by rewrite size_put | |].  
    + move => k Hk0 Hk1; rewrite initE ifT 1:/#; auto => />. case (i{2} * 32 <= k && k < i{2} * 32 + 32); move => *.
       - rewrite (nth_flatten witness 32). 
            * pose P := (fun (s : W8.t list) => size s = 32). (* Predicate *)
              pose L := (put sk{2} i{2} (to_list ith_seed{1})). (* List *)
              rewrite -(all_nthP P L witness) /P /L size_put sizeSK len_val /XMSS_WOTS_LEN.
              move => j Hj.       
              rewrite nth_put 1:/#. 
              case (i{2} = j); move => ?; [ by rewrite size_to_list | smt() ]. 
            * rewrite nth_put 1:/# ifT 1:/# get_to_list ; congr => /#. 
       - rewrite (nth_flatten witness 32). 
            * pose P := (fun (s : W8.t list) => size s = 32). (* Predicate *)
              pose L := (put sk{2} i{2} (to_list ith_seed{1})). (* List *)
              rewrite -(all_nthP P L witness) /P /L size_put sizeSK len_val /XMSS_WOTS_LEN. 
              move => j Hj.       
              rewrite nth_put 1:/#. 
              case (i{2} = j); move => ?; [ by rewrite size_to_list | smt() ]. 
            * rewrite nth_put 1:/# ifF 1:/# -nth_flatten; [| apply H0; 1:smt()].
              rewrite n_val /XMSS_N in H. 
              rewrite size_size; apply H. 
    + move => k Hk0.
      have ->: size (put sk{2} i{2} (to_list ith_seed{1})) = len by rewrite size_put /#.  
      rewrite nth_put 1:/#. 
      case (i{2} = k); move => *; [ rewrite size_to_list /# | apply H; rewrite sizeSK /# ]. 
qed.

lemma expand_seed_results (_in_seed _pub_seed : W8.t Array32.t, _addr : W32.t Array8.t) :
    len = XMSS_WOTS_LEN /\ 
    n = XMSS_N /\ 
    prf_padding_val = XMSS_HASH_PADDING_PRF /\
    prf_kg_padding_val = XMSS_HASH_PADDING_PRF_KEYGEN /\
    padding_len = XMSS_PADDING_LEN =>
    equiv [M(Syscall).__expand_seed ~ WOTS.pseudorandom_genSK :
      arg{1}.`2 = _in_seed /\ 
      arg{1}.`3 = _pub_seed /\
      arg{1}.`4 = _addr /\
      arg{2} = (to_list _in_seed, to_list _pub_seed, _addr) ==>
      res{1}.`1 = DecodeWotsSk res{2}.`1 /\
      size res{2}.`1 = len /\ 
      (forall (x : W8.t list), x \in res{2}.`1 => size x = n) /\
      res{1}.`2 = res{2}.`2].
proof.
admit. (* correctness & wots_sk_size from properties *)
qed.

(*** PK Gen : Done ***)
 
lemma pkgen_correct (_seed_ _pub_seed_ : W8.t Array32.t, _addr_ : W32.t Array8.t) :
    w = XMSS_WOTS_W /\
    len = XMSS_WOTS_LEN /\
    n = XMSS_N /\
    prf_padding_val = XMSS_HASH_PADDING_PRF /\
    prf_kg_padding_val = XMSS_HASH_PADDING_PRF_KEYGEN /\
    padding_len = XMSS_PADDING_LEN /\
    F_padding_val = XMSS_HASH_PADDING_F =>
    equiv [
      M(Syscall).__wots_pkgen ~ WOTS.pkGen :
      arg{1}.`2 = _seed_ /\
      arg{1}.`3 = _pub_seed_ /\
      arg{1}.`4 = _addr_ /\
      arg{2} = (to_list _seed_, to_list _pub_seed_, _addr_)
      ==>
      res{1}.`1 = DecodeWotsPk res{2}.`1 /\ 
      res{2}.`2 = res{1}.`2
    ]. 
proof.
rewrite /XMSS_N.
move => [#] ? len_val n_val *.
proc; auto => />. (* auto simplifies #pre and #post *)
swap {2} 3 3. 
seq 0 4 : (
  #pre /\
  size pk{2} = len /\
  size wots_skey{2} = len /\
  size pk_i{2} = n /\ 
  size sk_i{2} = n /\

  (forall (k : int), 0 <= k < len => size (nth witness pk{2} k) = n) /\
  (forall (k : int), 0 <= k < len => size (nth witness wots_skey{2} k) = n)
); first by auto => /> *; rewrite !size_nseq; do split;1..3:smt();smt(@List).
seq 2 1: (   
  sk_seed{2} = to_list seed{1} /\
  _seed{2} = to_list pub_seed{1} /\
  address{2} = addr{1} /\
  pk{1} = DecodeWotsSk wots_skey{2} /\

  size pk{2} = len /\
  size pk_i{2} = n /\ 
  size sk_i{2} = n /\
  size wots_skey{2} = len /\

  (forall (k : int), 0 <= k < len => size (nth witness pk{2} k) = n) /\
  (forall (k : int), 0 <= k < len => size (nth witness wots_skey{2} k) = n)
).
    + inline {1} M(Syscall).__expand_seed_ M(Syscall)._expand_seed. wp; sp.
      exists * inseed0{1}, pub_seed1{1}, addr1{1}; elim * => _P1 _P2 _P3; call {1} (expand_seed_results _P1 _P2 _P3); 1:smt(). 
      skip => /> &1 &2 H0 H1 H2 H3 H4 rL rR H5 H6 H7 H8. split; [ smt() | smt(@List) ]. 
conseq (: _ ==> address{2} = addr{1} /\ forall (k : int), 0 <= k < 2144 => pk{1}.[k] = nth witness (flatten pk{2}) k). 
    + auto => /> *; rewrite /DecodeWotsPk /of_list tP #smt:(@Array2144).
while (
  (* #pre but without the last expression *)
  sk_seed{2} = to_list seed{1} /\ 
  _seed{2} = to_list pub_seed{1} /\
  address{2} = addr{1} /\

  size pk{2} = len /\
  size wots_skey{2} = len /\
  size pk_i{2} = n /\ 
  size sk_i{2} = n /\

  (forall (k : int), 0 <= k < len => size (nth witness pk{2} k) = n) /\
  (forall (k : int), 0 <= k < len => size (nth witness wots_skey{2} k) = n) /\

  ={i} /\ 
  0 <= i{1} <= 67 /\

  (forall (k : int), 0 <= k < 32 * i{1} => pk{1}.[k] = nth witness (flatten pk{2}) k) /\
  (forall (k : int), 32 * i{1} <= k < 2144 => pk{1}.[k] = nth witness (flatten wots_skey{2}) k)
).
(* First subgoal of while *)
seq 2 1 : (#pre); first by inline {1}; auto.
seq 2 2 : (#pre /\ to_list t{1} = pk_i{2}).
    + inline M(Syscall).__gen_chain_inplace_ M(Syscall)._gen_chain_inplace; wp; sp. 
      exists * out0{1}, start0{1}, steps0{1}, addr1{1}, pub_seed1{1}.  
      elim * => _P1 _P2 _P3 _P4 _P5.  
      auto => />. 
      call (gen_chain_inplace_correct _P1 _P2 _P3 _P4 _P5).
      skip => /> &1 &2 ? HsizeSK ??? Hsize ??? T *; do split; 2: smt(); last first.
           * move => H0 H1 H2 H3 rL rR H4 H5; do split; 1,4:smt(); [ rewrite H4 size_to_list /# | apply Hsize => /# ]. 
           * apply (eq_from_nth witness); [ rewrite size_to_list -n_val; apply Hsize => /# |].
             move => j. 
             have ->: size (nth witness wots_skey{2} i{2}) = 32 by smt(). 
             move => Hj.
             rewrite -List.nth_flatten 1,2:/#.
             rewrite sumzE BIA.big_map /(\o) //=.
             rewrite -(StdBigop.Bigint.BIA.eq_big_seq (fun _ => 32)) /=. 
               - apply all_take; first by rewrite HsizeSK len_val /XMSS_WOTS_LEN /#.
                 auto => />. 
                 rewrite -size_all; apply size_size => /#.
             rewrite big_constz count_predT.
             have ->: size (take i{2} wots_skey{2}) = i{2} by smt(size_take).
             rewrite initE ifT 1:/#; auto => /> /#. 
auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.
do split;3,4,7,8:smt().
    + rewrite size_put /#.
    + move => *; rewrite nth_put /#. 
    + move => k Hk0 Hk1. rewrite initE ifT 1:/#. auto => />. 
      case (i{2} * 32 <= k && k < i{2} * 32 + 32); move => *.
        - rewrite (nth_flatten witness 32). 
           + rewrite allP; apply all_put; auto => />; [ rewrite size_to_list // |]. 
             auto => />; rewrite -size_all_r size_size /#. 
          rewrite nth_put 1:/# ifT 1:/#. 
          rewrite get_to_list; congr => /#.
        - rewrite (nth_flatten witness 32). 
            + rewrite allP. 
              apply all_put; [ auto => />; rewrite size_to_list // |]. 
          auto => />. rewrite -size_all_r size_size /#. 
          rewrite nth_put 1:/# ifF 1:/#. 
          rewrite -nth_flatten 2:/# size_size /#.
    + move => *; rewrite initE ifT /#. 
(* Last subgoal of while *)
auto => /> *; do split; [| | by rewrite len_val | smt(@Array2144 @List)];
move => k Hk0 Hk1; rewrite /DecodeWotsSk get_of_list /#.
qed.

(*** Pk From Sig : Doing ***)

op load_sig (mem : global_mem_t) (ptr : W64.t) : W8.t Array2144.t =
  Array2144.init(fun i => loadW8 mem (to_uint ptr + i)).

lemma pk_from_sig_correct (mem : global_mem_t) (_sig_ptr_ : W64.t, _msg_ _pub_seed_ : W8.t Array32.t, _addr_ : W32.t Array8.t) :
    valid_ptr_i _sig_ptr_ 2144 =>
    n = XMSS_N /\
    floor (log2 w%r) = XMSS_WOTS_LOG_W /\ 
    w = XMSS_WOTS_W /\
    len1 = XMSS_WOTS_LEN1 /\ 
    len2 = XMSS_WOTS_LEN2 /\
    len = XMSS_WOTS_LEN /\
    prf_padding_val = XMSS_HASH_PADDING_PRF /\
    padding_len = XMSS_PADDING_LEN /\ 
    F_padding_val = XMSS_HASH_PADDING_F =>
    equiv [
      M(Syscall).__wots_pk_from_sig ~ WOTS.pkFromSig :
      arg{1}.`2 = _sig_ptr_ /\
      arg{1}.`3 = _msg_ /\
      arg{1}.`4 = _pub_seed_ /\ 
      arg{1}.`5 = _addr_ /\ 
      Glob.mem{1} = mem /\
      arg{2} = (to_list _msg_, EncodeWotsSignature (load_sig mem _sig_ptr_), to_list _pub_seed_, _addr_) /\
      Glob.mem{2} = mem
      ==>
      res{1}.`1 = DecodeWotsPk res{2}.`1 /\ 
      res{1}.`2 = res{2}.`2
    ].
proof.
rewrite /XMSS_N /XMSS_WOTS_LOG_W /XMSS_WOTS_W /XMSS_WOTS_LEN1 /XMSS_WOTS_LEN2.
move => ? [#] n_val logw_val w_val len1_val len2_val *.
proc; auto => />. 
conseq (: _ ==> 
  address{2} = addr{1} /\ 
  forall (k : int), 0 <= k < 2144 => pk{1}.[k] = nth witness (flatten tmp_pk{2}) k
); first by auto => /> *; rewrite /DecodeWotsPk /of_list tP; smt(@Array2144).

seq 1 1 : (
  sig_ptr{1} = _sig_ptr_ /\
  addr{1} = address{2} /\
  M{2} = to_list msg{1} /\
  _seed{2} = to_list pub_seed{1} /\
  sig{2} = EncodeWotsSignature (load_sig mem sig_ptr{1}) /\

  size tmp_pk{2} = 67 /\
  (forall (t : W8.t list), t \in tmp_pk{2} => size t = 32) /\

  Glob.mem{1} = mem /\ Glob.mem{2} = mem /\
  valid_ptr_i sig_ptr{1} 2144
); first by auto => />; split; [by rewrite size_nseq /# | smt(@List)].

inline M(Syscall).__chain_lengths_ M(Syscall)._chain_lengths M(Syscall).__chain_lengths.

seq 11 0 : (#pre /\ lengths2{1} = lengths{1} /\ msg2{1} = msg{1}); first by auto.

seq 1 1 : (
  M{2} = to_list msg{1} /\
  _seed{2} = to_list pub_seed{1} /\
  address{2} = addr{1} /\
  size sig{2} = 67 /\
  size (flatten sig{2}) = 2144 /\
  (forall (t : W8.t list), t \in sig{2} => size t = 32) /\ 
  size M{2} = 32 /\
  sig{2} = EncodeWotsSignature (load_sig mem sig_ptr{1}) /\
  lengths2{1} = lengths{1} /\ 

  msg{2} = map (W32.to_uint) (to_list t0{1}) /\
  (forall (k : int), 0 <= k < 64 => 0 <= to_uint t0{1}.[k] < w) /\

  size tmp_pk{2} = 67 /\
  (forall (t : W8.t list), t \in tmp_pk{2} => size t = 32) /\
  

  Glob.mem{1} = mem /\ Glob.mem{2} = mem /\
  valid_ptr_i sig_ptr{1} 2144
).
    + exists * msg2{1}; elim * => P; call (base_w_results_64 P) => //=.
      skip => /> *; do split.
         * rewrite /EncodeWotsSignature size_chunk //= size_to_list //.
         * rewrite /EncodeWotsSignature size_flatten sumzE BIA.big_map /(\o) //= -(StdBigop.Bigint.BIA.eq_big_seq (fun _ => 32)) 1:#smt:(@List @BitChunking).
           rewrite  big_constz count_predT size_chunk //= size_to_list //=.  
         * rewrite /EncodeWotsSignature => />; smt(@List @BitChunking).
         * by rewrite size_to_list. 

seq 2 0 : (
  M{2} = to_list msg{1} /\
  _seed{2} = to_list pub_seed{1} /\
  address{2} = addr{1} /\
  size sig{2} = 67 /\
  size (flatten sig{2}) = 2144 /\
  (forall (t2 : W8.t list), t2 \in sig{2} => size t2 = 32) /\
  size M{2} = 32 /\
  sig{2} = EncodeWotsSignature (load_sig mem sig_ptr{1}) /\
  msg{2} = map W32.to_uint (to_list t0{1}) /\
  (forall (k : int), 0 <= k < 64 => 0 <= to_uint t0{1}.[k] < w) /\

  (forall (k : int), 0 <= k < 64 => to_uint lengths2{1}.[k] = nth witness msg{2} k) /\

  size tmp_pk{2} = 67 /\
  (forall (t : W8.t list), t \in tmp_pk{2} => size t = 32) /\
  

  Glob.mem{1} = mem /\ Glob.mem{2} = mem /\
  valid_ptr_i sig_ptr{1} 2144
).
    + auto => /> *.
      rewrite (nth_map witness); [by rewrite size_to_list |].
      rewrite initiE 1:/# => />. 
      rewrite ifT //=.  

inline {1} M(Syscall).__wots_checksum.
seq 5 0 : (#pre /\ csum_base_w{1} = t1{1} /\ msg_base_w{1} = lengths2{1}); first by auto.

seq 1 0 : (
  #pre /\
  (forall (k : int), 0 <= k < 64 => 0 <= to_uint buf{1}.[k] < w) /\
  msg{2} = map (W32.to_uint) (to_list buf{1})
).
    + auto => /> &1 &2 ????? H4 *; do split => [ * |]. do split.
          - rewrite initiE //= H4 // (nth_map witness); [ by rewrite size_to_list //= |].
            rewrite get_to_list /#.
          - rewrite initiE //= H4 //= (nth_map witness); [ by rewrite size_to_list //= |].
            rewrite get_to_list /#.
          - apply (eq_from_nth witness); [ by rewrite !size_map !size_iota |].
            rewrite size_map size_to_list => i Hi.
            rewrite -H4 //= (nth_map witness); [ by rewrite size_to_list |]. 
            rewrite get_to_list //= initiE //=.

seq 1 1 : (#pre /\ to_uint csum{1} = csum{2} /\ 0 <= csum{2} <= len1 * (w - 1)).
    + exists * buf{1}; elim * => P; call {1} (wots_checksum_results P) => //.
      skip => /> /#.

seq 3 0 : (#pre /\ u{1} = W64.of_int 4); first by auto.

seq 2 2 : (
  M{2} = to_list msg{1} /\
  _seed{2} = to_list pub_seed{1} /\
  address{2} = addr{1} /\
  size sig{2} = 67 /\
  size (flatten sig{2}) = 2144 /\
  (forall (t2 : W8.t list), t2 \in sig{2} => size t2 = 32) /\
  size M{2} = 32 /\
  sig{2} = EncodeWotsSignature (load_sig mem sig_ptr{1}) /\
  msg{2} = map W32.to_uint (to_list t0{1}) /\
  
  (forall (k0 : int), 0 <= k0 < 64 => 0 <= to_uint t0{1}.[k0] < w) /\
  (forall (k0 : int), 0 <= k0 < 64 => to_uint lengths2{1}.[k0] = nth witness msg{2} k0) /\
  csum_base_w{1} = t1{1} /\ 
  msg_base_w{1} = lengths2{1} /\
  (forall (k0 : int), 0 <= k0 < 64 => 0 <= to_uint buf{1}.[k0] < w) /\
  msg{2} = map W32.to_uint (to_list buf{1}) /\
  0 <= csum{2} <= len1 * (w - 1) /\
  u{1} = (of_int 4)%W64 /\

  to_uint csum{1} = to_uint csum_32{2} /\


  size tmp_pk{2} = 67 /\
  (forall (t : W8.t list), t \in tmp_pk{2} => size t = 32) /\
  

  Glob.mem{1} = mem /\ Glob.mem{2} = mem /\
  valid_ptr_i sig_ptr{1} 2144
).
    + auto => /> &1 &2 *. 
      rewrite (: 63 = 2^6 - 1) 1:/# and_mod //=. 
      have ->: truncateu8 ((of_int 4))%W64 = W8.of_int 4 by smt(@W64 pow2_64).
      rewrite !shl_shlw //= len2_val w_val.
      have ->: floor (log2 16%r) = 4 by rewrite log2_16 from_int_floor.
      by simplify.
      have ->: floor (log2 16%r) = 4 by rewrite log2_16 from_int_floor.
      simplify.
      rewrite !to_uint_shl //= of_uintK //=.
      have ->: to_uint csum{1} %% 4294967296 = to_uint csum{1} by smt(@W64 pow2_64 @IntDiv).
      smt(@IntDiv).

seq 0 1 : (#pre /\ len_2_bytes{2} = 2).
    + auto => /> *. 
      rewrite w_val len2_val log2_16 -fromintM //= from_int_ceil //=; apply ceil_3_2.

seq 1 1 : (#pre /\ to_list csum_bytes_p{1} = csum_bytes{2}).
    + ecall {1} (ull_to_bytes_2_equiv csum{1}). 
      auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 rL H15 *.
      rewrite H15 //=; congr; smt(@W32). 

seq 1 1 : (
  M{2} = to_list msg{1} /\
  _seed{2} = to_list pub_seed{1} /\
  address{2} = addr{1} /\
  size sig{2} = 67 /\
  size (flatten sig{2}) = 2144 /\
  (forall (t2 : W8.t list), t2 \in sig{2} => size t2 = 32) /\
  size M{2} = 32 /\
  sig{2} = EncodeWotsSignature (load_sig mem sig_ptr{1}) /\
  msg{2} = map W32.to_uint (to_list t0{1}) /\
  
  (forall (k0 : int), 0 <= k0 < 64 => 0 <= to_uint t0{1}.[k0] < w) /\
  
  (forall (k0 : int), 0 <= k0 < 64 => to_uint lengths2{1}.[k0] = nth witness msg{2} k0) /\
  
  msg_base_w{1} = lengths2{1} /\
  
  (forall (k0 : int), 0 <= k0 < 64 => 0 <= to_uint buf{1}.[k0] < w) /\
  
  msg{2} = map W32.to_uint (to_list buf{1}) /\
  
  0 <= csum{2} <= len1 * (w - 1) /\
  
  u{1} = (of_int 4)%W64 /\ 
  to_uint csum{1} = to_uint csum_32{2} /\

  len_2_bytes{2} = 2 /\
  to_list csum_bytes_p{1} = csum_bytes{2} /\

  csum_base_w{2} = map (W32.to_uint) (to_list csum_base_w{1}) /\
  (forall (k : int), 0 <= k < 3 => 0 <= to_uint csum_base_w{1}.[k] < w) /\

  size tmp_pk{2} = 67 /\
  (forall (t : W8.t list), t \in tmp_pk{2} => size t = 32) /\

  Glob.mem{1} = mem /\ Glob.mem{2} = mem /\
  valid_ptr_i sig_ptr{1} 2144
).
    + exists * csum_bytes_p{1}; elim * => P; call (base_w_results_3 P) => //=.
      auto => /> *; smt(array3_map_bounds).

seq 6 1 : (
  M{2} = to_list msg{1} /\
  _seed{2} = to_list pub_seed{1} /\
  address{2} = addr{1} /\
  size sig{2} = 67 /\
  size (flatten sig{2}) = 2144 /\
  (forall (t2 : W8.t list), t2 \in sig{2} => size t2 = 32) /\
  size M{2} = 32 /\
  sig{2} = EncodeWotsSignature (load_sig mem sig_ptr{1}) /\
  
  0 <= csum{2} <= len1 * (w - 1) /\
  to_uint csum{1} = to_uint csum_32{2} /\
  to_list csum_bytes_p{1} = csum_bytes{2} /\

  csum_base_w{2} = map W32.to_uint (to_list csum_base_w{1}) /\  
  (forall (k0 : int), 0 <= k0 < 3 => 0 <= to_uint csum_base_w{1}.[k0] < w) /\

  map W32.to_uint (to_list lengths{1}) = msg{2} /\
  (forall (k : int), 0 <= k < 67 => 0 <= to_uint lengths{1}.[k] < w) /\
  
  size tmp_pk{2} = 67 /\
  (forall (t : W8.t list), t \in tmp_pk{2} => size t = 32) /\

  Glob.mem{1} = mem /\ Glob.mem{2} = mem /\
  valid_ptr_i sig_ptr{1} 2144
).
    + auto => /> &1 &2 ????? H5 * ; do split.
        * apply (eq_from_nth witness); [ rewrite size_cat !size_map !size_iota //= |].
          rewrite size_map size_to_list => i?.
          rewrite nth_cat !size_map size_iota (: max 0 64 = 64) 1:/#. 
          case (0 <= i < 64).
              - move => ?.  
                rewrite ifT 1:/# (nth_map witness); [by rewrite size_to_list |]. 
                rewrite get_to_list initiE 1:/# => />.  
                rewrite ifF 1:/# H5 //=.
              - move => ?. 
                rewrite ifF 1:/# (nth_map witness); [ by rewrite size_to_list |]. 
                rewrite get_to_list initiE 1:/# => />. 
                rewrite ifT 1:/# (nth_map witness); [ by rewrite size_to_list /# |]. 
                rewrite get_to_list //=. 
        * move => k??; do split.             
              - rewrite initiE 1:/# => />.
                case (0 <= k < 64).  
                    + move => ?. rewrite ifF 1:/# H5 //=.  
                      rewrite (nth_map witness); [ by rewrite size_to_list |]. 
                      rewrite get_to_list /#. 
                    + move => ?; rewrite ifT /#.
              - move => ?.            
                rewrite initiE //=.
                case (0 <= k < 64).  
                    + move => ?. 
                      rewrite ifF 1:/# H5 //.  
                      rewrite (nth_map witness); [ by rewrite size_to_list |]. 
                      rewrite get_to_list /#. 
                    + move => ?; rewrite ifT /#.

(*** O ciclo while comeca aqui ***)
while (
  ={i} /\ 
  0 <= i{1} <= 67 /\
  #pre /\
  (forall (k : int), 0 <= k < 32 * i{1} => pk{1}.[k] = nth witness (flatten tmp_pk{2}) k) (* parte consumida *)
); last by auto => /> /#.

seq 2 1 : (#pre); first by inline{1}; auto.

seq 1 1 : (
  #pre /\ 
  start{1} = lengths{1}.[i{1}] /\
  to_uint start{1} = msg_i{2} /\
  0 <= msg_i{2} < w /\
  0 <= to_uint start{1} < w
).
    + auto => /> &1 &2 *; rewrite (nth_map witness); [ by rewrite size_to_list |]. 
      rewrite get_to_list //= /#. 
 
seq 4 0 : (
  #pre /\ 
  steps{1} = (W32.of_int 15) - lengths{1}.[i{2}] /\
  0 <= to_uint (start{1} + steps{1}) < w /\
  t{1} = sig_ptr{1} + W64.of_int (i{1} * 32)
).

auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 *; do split => [| ?].
    * rewrite to_uintD ; smt(@W32 pow2_32). 
    * have ->: lengths{1}.[i{2}] + ((of_int 15)%W32 - lengths{1}.[i{2}]) =  (of_int 15)%W32 by ring. 
      rewrite of_uintK w_val //=. 

seq 1 1 : (
  #pre /\
  to_list aux_0{1} = sig_i{2}
). 
    + exists * t{1} ; elim * => P.
      ecall {1} (p_memcpy_ptr_correct P).
      auto => /> &1 &2 *; do split; 1..3: smt(@W64 pow2_64).
      move => *. 
      rewrite /EncodeWotsSignature /load_sig; apply (eq_from_nth witness). 
          * rewrite size_to_list size_nth_chunk //= size_to_list /#. 
          * rewrite size_to_list => i? />. 
            rewrite initiE //= /chunk nth_mkseq; [by rewrite size_to_list /# |] => />. 
            rewrite nth_take //= 1:/# nth_drop 1,2:/# get_to_list initiE 1:/# => />.                
            congr; smt(@W64 pow2_64). 
(*** tou aqui **)
seq 2 1 : (
    ={i} /\
    0 <= i{1} && i{1} <= 67 /\
M{2} = to_list msg{1} /\
_seed{2} = to_list pub_seed{1} /\
address{2} = addr{1} /\
size sig{2} = 67 /\
size (flatten sig{2}) = 2144 /\
(forall (t2 : W8.t list), t2 \in sig{2} => size t2 = 32) /\
size M{2} = 32 /\
sig{2} = EncodeWotsSignature (load_sig mem sig_ptr{1}) /\
(0 <= csum{2} && csum{2} <= len1 * (w - 1)) /\
to_uint csum{1} = to_uint csum_32{2} /\
to_list csum_bytes_p{1} = csum_bytes{2} /\
-csum_base_w{2} = map W32.to_uint (to_list csum_base_w{1}) /\
(forall (k0 : int), 0 <= k0 < 3 => 0 <= to_uint csum_base_w{1}.[k0] < w) /\
map W32.to_uint (to_list lengths{1}) = msg{2} /\
(forall (k0 : int), 0 <= k0 < 67 => 0 <= to_uint lengths{1}.[k0] < w) /\
Glob.mem{1} = mem /\ 
Glob.mem{2} = mem /\ 
valid_ptr_i sig_ptr{1} 2144 /\
(forall (k0 : int), 0 <= k0 < 32 * i{1} => pk{1}.[k0] = nth witness (flatten tmp_pk{2}) k0) /\
i{1} < 67 /\ 
i{2} < len /\
    to_list aux_0{1} = pk_i{2} /\
    aux_1{1} = address{2}
).
    + inline M(Syscall).__gen_chain_inplace_ M(Syscall)._gen_chain_inplace; wp; sp. 
      exists * out0{1}, start0{1}, steps0{1}, addr1{1}, pub_seed1{1}.  
      elim * => _P1 _P2 _P3 _P4 _P5 *.  
      call (gen_chain_inplace_correct _P1 _P2 _P3 _P4 _P5) => [/# |].
      skip => /> &1 &2 *; do split; first last.
          * admit.
          * smt(). 
          * smt(@W32 pow2_32). 
          * admit. 
          * smt(@W32 pow2_32). 
          * move => [#] *; split. admit. admit.
          * apply (eq_from_nth witness); rewrite !size_to_list //= => i?.
            admit. 

auto => /> &1 &2 *; do split;1,2,4,5:smt(). 
move => k0??.
rewrite initiE 1:/# => />. 
rewrite (nth_flatten witness 32).
    + rewrite size_all_r; apply all_put => />; [ by rewrite size_to_list |]. admit. 
case: (i{2} * 32 <= k0 && k0 < i{2} * 32 + 32) => H.
  + rewrite nth_put. admit. rewrite ifT 1:/# get_to_list /#. 
  + rewrite nth_put. admit. rewrite ifF 1:/# -nth_flatten. admit.  smt(). 
qed.
        
