pragma Goals : printall.

require import AllCore List RealExp IntDiv.

from Jasmin require import JModel JArray.

require import Params Address Hash BaseW WOTS. 

require import XMSS_IMPL Parameters.

require import Array2 Array3 Array8 Array32 Array64 Array67 Array96 Array2144.

require import WArray32.

require import Correctness_Bytes Correctness_Mem Correctness_Address Correctness_Hash. 
require import Repr2.
require import Utils2.

require import BitEncoding.
(*---*) import BitChunking.

require import StdBigop. 
(*---*) import Bigint.


(** -------------------------------------------------------------------------------------------- **)

op load_sig (mem : global_mem_t) (ptr : W64.t) : W8.t Array2144.t =
  Array2144.init(fun i => loadW8 mem (to_uint ptr + i)).

(** -------------------------------------------------------------------------------------------- **)

lemma nbyte_xor_val (a b : nbytes): 
    val (nbytexor a b) = bytexor (val a) (val b).
proof.
rewrite /nbytexor NBytes.insubdK //= /P /bytexor size_map size_zip !valP //.
qed.

(** -------------------------------------------------------------------------------------------- **)

lemma zip_fst (a b : W8.t list) (i : int):
  0 <= i < min (size a) (size b) =>
    (nth witness (zip a b) i).`1 = nth witness a i 
      by smt(@List).

lemma zip_snd (a b : W8.t list) (i : int):
  0 <= i < min (size a) (size b) =>
    (nth witness (zip a b) i).`2 = nth witness b i 
      by smt(@List).

(** -------------------------------------------------------------------------------------------- **)

lemma simplify_pow (a b : int) : 
    0 < a /\ 0 < b => 
      a%r ^ b%r = (a ^ b)%r.
proof.
move => [#] ??.
rewrite -RField.fromintXn 1:/# #smt:(@RealExp).
qed.

hint simplify simplify_pow. 

lemma log2_16 : log2 16%r = 4%r.
proof.
have ->: 16%r = 2%r ^ 4%r by simplify.
rewrite /log2 logK /#.
qed.

(** -------------------------------------------------------------------------------------------- **)

module ThashF = {
  proc thash_f (t : nbytes, seed : seed, address : adrs) : (nbytes * adrs) = {
    var key : nbytes;
    var bitmask : nbytes;
    var addr_bytes : nbytes;
    
    addr_bytes <- addr_to_bytes address;
    key <@ Hash.prf(addr_bytes, seed);
    address <- set_key_and_mask address 1;
    addr_bytes <- addr_to_bytes address;
    bitmask <@ Hash.prf(addr_bytes, seed);
    t <@ Hash._F(key, nbytexor t bitmask);
    return (t, address);
  }
}.

lemma thash_f_equiv (_out_ _seed_ : W8.t Array32.t) (a : W32.t Array8.t) :
    n = XMSS_N /\
    prf_padding_val = XMSS_HASH_PADDING_PRF /\
    padding_len = XMSS_PADDING_LEN /\ 
    F_padding_val = XMSS_HASH_PADDING_F =>
    equiv [
      M(Syscall).__thash_f ~ ThashF.thash_f :
      arg{1}.`1 = _out_ /\
      arg{1}.`2 = _seed_ /\
      arg{1}.`3 = a /\
      
      arg{2}.`1 = NBytes.insubd (to_list _out_) /\
      arg{2}.`2 = NBytes.insubd (to_list _seed_) /\
      arg{2}.`3 = a
      ==>
      to_list res{1}.`1 = val res{2}.`1 /\
      res{1}.`2 = res{2}.`2 /\
      res{1}.`2.[7] = W32.one /\
      sub res{1}.`2 0 7 = sub a 0 7
    ].
proof. 
rewrite /XMSS_N. 
move => [#] n_val ???.
proc => /=.
seq 4 0 : #pre; first by auto.

seq 1 1 : (#pre /\ to_list addr_as_bytes{1} = val addr_bytes{2}).
  + by ecall {1} (addr_to_bytes_correctness addr{1}); auto.

inline {2} Hash._F. 

swap {2} 7 -6.

seq 2 1 : (#pre /\ to_list padding{1} = padding{2}).
  + auto.
    ecall {1} (ull_to_bytes_32_correct W64.zero).
    auto => /> &1 &2 ??->. 
    congr => /#.

seq 1 0 : (#pre /\ sub buf{1} 0 n = padding{2}).
  + auto => /> &1 &2 ?.
    apply (eq_from_nth witness); first by rewrite size_to_list n_val size_sub.
    rewrite n_val size_sub // => j?.
    by rewrite get_to_list nth_sub // initiE 1:/# /= ifT.

seq 1 1 : (#pre /\ to_list aux{1} = val key{2}).
  + inline {1} M(Syscall).__prf_ M(Syscall)._prf; wp; sp.
    exists * in_00{1}, key0{1}; elim * => _P1 _P2.
    call {1} (prf_correctness _P1 _P2) => [/# |]. 
    skip => /> &1 &2 H0 H1.
    split; [smt(@NBytes) | smt()].

seq 1 0 : (#pre /\ sub buf{1} n n = val key{2}).
  + auto => /> &1 &2 H0 H1 H2. 
    split.
      - apply (eq_from_nth witness); first by rewrite n_val size_to_list size_sub.
        rewrite n_val size_sub // => j?.
        by rewrite -H1 nth_sub //= initiE 1:/# /= ifF 1:/# nth_sub // n_val .
      - apply (eq_from_nth witness); first by rewrite valP n_val size_sub.
        rewrite n_val size_sub // => j?.
        by rewrite nth_sub // initiE 1:/# /= ifT 1:/# -get_to_list H2. 

seq 1 1 : (
  #{/~addr{1} = a}{/~address{2} = a}pre /\ 
  addr{1} = address{2} /\ 
  addr{1}.[7] = W32.one /\
  sub addr{1} 0 7 = sub a 0 7
).
  + inline {1}; auto => /> &1 &2 H0 H1 H2 H3*.
    apply (eq_from_nth witness); first by rewrite !size_sub.
    rewrite size_sub // => j?.
    by rewrite !nth_sub //= get_setE //= ifF 1:/#.

seq 1 1 : (#pre /\ to_list addr_as_bytes{1} = val addr_bytes{2}).
  + by ecall {1} (addr_to_bytes_correctness addr{1}); auto. 

seq 1 1 : (#pre /\ to_list bitmask{1} = val bitmask{2}).
  + inline {1} M(Syscall).__prf_ M(Syscall)._prf; wp; sp.
    exists * in_00{1}, key0{1}; elim * => _P1 _P2.
    call {1} (prf_correctness _P1 _P2) => [/# |]. 
    skip => /> &1 &2 H0 H1 H2 H3 H4 *. 
    split; [smt(@NBytes) | smt()]. 

seq 2 3 : (
  addr{1} = address{2} /\
  addr{1}.[7] = W32.one /\
  sub addr{1} 0 7 = sub a 0 7 /\
  to_list buf{1} = buf{2}
); last first.
  + auto.
    inline {1} M(Syscall).__core_hash__96 M(Syscall)._core_hash_96.
    by wp; sp; ecall {1} (hash_96 in_00{1}); auto => />. 

wp; sp.
 
while {1} 
(
  addr{1} = address{2} /\ 
  addr{1}.[7] = W32.one /\
  sub addr{1} 0 7 = sub a 0 7 /\
  0 <= to_uint i{1} <= 32 /\
  to_list bitmask{1} = val bitmask{2} /\
  to_list out{1} = val t{2} /\
  sub buf{1} 0 n = padding{2} /\
  sub buf{1} n n = val key{2} /\
  sub buf{1} (n + n) (to_uint i{1}) = sub_list (val (nbytexor t{2} bitmask{2})) 0 (to_uint i{1}) 
)
(32 - to_uint i{1}); last first.
  + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 *.
    do split. 
      - by rewrite  insubdK // /P size_to_list n_val.
      - apply (eq_from_nth witness); first by rewrite size_sub_list // size_sub.
        rewrite size_sub // => j? /#.
      - move => bufL iL.
        split => [* |]; first by rewrite ultE /#.
        rewrite ultE of_uintK n_val /= => ??? H6 H7 H8 H9 *.
        apply (eq_from_nth witness); first by by rewrite !size_cat !size_to_list !valP n_val.
        rewrite size_to_list => j?.
        case (0 <= j < 32) => ?.
           + rewrite get_to_list.
             have ->: bufL.[j] = nth witness (sub bufL 0 32) j by rewrite nth_sub.
             by rewrite H6 !nth_cat !size_cat !size_to_list !valP n_val /= ifT 1:/# ifT 1:/# H7 get_to_list.
        case (32 <= j < 64) => ?.
           + rewrite get_to_list.
             have ->: bufL.[j] = nth witness (sub bufL 32 32) (j - 32) by rewrite nth_sub /#.
             by rewrite H8 !nth_cat !size_cat !size_to_list !valP n_val /= ifT 1:/# ifF 1:/#.
        rewrite get_to_list.
        have ->: bufL.[j] = nth witness (sub bufL 64 (to_uint iL)) (j - 64) by rewrite nth_sub /#.
        rewrite H9 !nth_cat !size_cat !size_to_list !valP n_val /= ifF 1:/#.
        by rewrite /sub_list nth_mkseq 1:/#.

auto => /> &hr H0 H1 H2 H3 H4 H5 H6 H7 H8 *.
do split; 1,2,6: by smt(@W64 pow2_64).
  - apply (eq_from_nth witness); first by rewrite !size_sub /#.
    rewrite size_sub 1:/# => j?.        
    rewrite !nth_sub //= get_setE; first by smt(@W64 pow2_64).
    rewrite ifF // to_uintD of_uintK /=/#.
  - apply (eq_from_nth witness); first by rewrite valP size_sub /#.
    rewrite size_sub 1:/# => j?.        
    rewrite !nth_sub //= get_setE; first by smt(@W64 pow2_64).
    rewrite ifF; first by rewrite to_uintD of_uintK /=/#.
    rewrite -H6 n_val /= nth_sub /#.
  - apply (eq_from_nth witness); first by rewrite size_sub to_uintD_small 1..3:/# size_sub_list /#.
    rewrite size_sub to_uintD_small 1..3:/# => j?.
    rewrite nth_sub // /sub_list nth_mkseq // /= get_setE; first by smt(@W64 pow2_64).
    case (to_uint i{hr} = j) => H; [rewrite ifT; first by smt(@W64 pow2_64) | rewrite ifF; first by smt(@W64 pow2_64)]; last first.
        + rewrite n_val /=.
          have ->: buf{hr}.[64 + j] = nth witness (sub buf{hr} (n + n) (to_uint i{hr})) j by rewrite nth_sub 2:/#; smt(@W64 pow2_64).
          rewrite H7 /sub_list nth_mkseq 2:/#; smt(@W64 pow2_64).
        + rewrite /nbytexor insubdK /bytexor; first by rewrite /P size_map size_zip !valP.
          rewrite (nth_map witness) /=. 
             - rewrite size_zip !valP n_val (: min 32 32 = 32) 1:/#; smt(@W64 pow2_64).
               rewrite zip_fst; first by rewrite !valP n_val /=; smt(@W64 pow2_64).
               rewrite zip_snd; first by rewrite !valP n_val /=; smt(@W64 pow2_64).
               rewrite -H4 -!get_to_list H; congr. (* this gets rid of the rhs *)
               congr.               
qed.

(** -------------------------------------------------------------------------------------------- **)

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
rewrite /XMSS_WOTS_W /XMSS_WOTS_LOG_W => [#] logw_val w_val.
proc.
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
  (forall (j : int), 0 <= j < to_uint out{1} => (to_uint output{1}.[j]) = nth witness base_w{2} j) /\
  (forall (j : int), 0 <= j < to_uint out{1} => 0 <= to_uint output{1}.[j] < w)
); last first.
    + auto => /> &1.
      do split; 2,3: by smt().
         * by rewrite size_nseq.
         * move => bitsL inL outL resultL resultR H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.
           split => [| /#].
           apply (eq_from_nth witness); first by rewrite H4 size_map size_to_list.
           rewrite H4 => i?.
           rewrite (nth_map witness). 
              - by rewrite size_to_list.
           rewrite get_to_list H9 //#.
if.
    + auto => /> &1 &2 *; smt(@W64).
    + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9. 
      do split; 1,2,11: by smt().
        * by rewrite size_put.
        * rewrite to_uintD /#.
        * rewrite to_uintD /#.
        * rewrite to_uintD /#.
        * rewrite to_uintD /#.
        * by rewrite logw_val.
        * rewrite logw_val /=/#.
        * rewrite to_uintD /#.
        * rewrite to_uintD_small 1:/# /= => j??.
          rewrite nth_put 1:/# get_setE //.
          case (j = to_uint out{1}) => [-> |?]; last first.
               - rewrite ifF 1:/# H7 //#.
          rewrite w_val ifT // log2_16 from_int_floor /= (: 15 = 2 ^ 4 - 1) 1:/# !and_mod //.
          rewrite (: 31 = 2 ^ 5 - 1) 1:/# !shr_div !of_uintK and_mod //=.
          smt(modz_small).
        * rewrite to_uintD_small 1:/# /= => j??.
          rewrite (: 31 = 2 ^ 5 - 1) 1:/# !and_mod // of_uintK.
          rewrite get_setE //.
          case (j = to_uint out{1}) => [?| /#].
          rewrite (: 15 = 2 ^ 4 - 1) 1:/# !and_mod // of_uintK.
          smt(modz_small).
    + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.
      do split; 1,2: by smt().
        * by rewrite size_put.
        * rewrite to_uintD /#.
        * rewrite to_uintD /#.
        * rewrite to_uintD /#.
        * rewrite to_uintD /#.
        * rewrite logw_val to_uintB // #smt:(@W64 pow2_64 modz_small).
        * rewrite logw_val H5 /= #smt:(@W64 pow2_64 modz_small).
        * rewrite H6 #smt:(@W64 pow2_64 @IntDiv).  
        * rewrite to_uintD_small 1:/# /= => j??.
          rewrite nth_put 1:/# get_setE //.
          case (j = to_uint out{1}) => [-> |?]; last first.
             - rewrite ifF 1:/# H7 //#.
          rewrite ifT // logw_val w_val /= (: 15 = 2^4 - 1) 1:/# (: 31 = 2^5 - 1) 1:/# !and_mod // !of_uintK //=.
          rewrite to_uint_shr.
             - rewrite !of_uintK /#.
          rewrite to_uint_shr.
             - rewrite !of_uintK /#.
         rewrite to_uint_truncateu8 to_uint_zeroextu32 !of_uintK /=. 
         smt(@IntDiv @W64 pow2_64 modz_small).
        * rewrite to_uintD_small 1:/# /= => j??. 
          rewrite (: 31 = 2^5 - 1) 1:/# (: 15 = 2^4 - 1) 1:/# !and_mod //=.        
          rewrite to_uint_shr.
             - rewrite !of_uintK /#.
          rewrite get_setE //.
          case (j = to_uint out{1}) => [?| /#].
          rewrite to_uint_zeroextu32 to_uint_truncateu8 !of_uintK #smt:(modz_small).
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
      forall (k : int), 0 <= k < 3 => 0 <= to_uint res{1}.[k] < w
    ].
proof.
rewrite /XMSS_WOTS_W /XMSS_WOTS_LOG_W => [#] logw_val w_val.
proc.
sp.
while (
  ={total, consumed} /\ 0 <= consumed{1} <= 3 /\
  size base_w{2} = 3 /\
  outlen{2} = 3 /\
  out{2} = to_uint out{1} /\
  out{2} = consumed{1} /\
  X{2} = to_list input{1} /\
  out{2} = to_uint out{1} /\ 0 <= to_uint out{1} <= 67 /\
  bits{2} = to_uint bits{1} /\ 
  bits{2} = consumed{2} %% 2 * 4 /\
  _in{2} = to_uint in_0{1} /\ _in{2} = (consumed{2} + 1) %/ 2 /\
  (forall (j : int), 0 <= j < to_uint out{1} => (to_uint output{1}.[j]) = nth witness base_w{2} j) /\
  (forall (j : int), 0 <= j < to_uint out{1} => 0 <= to_uint output{1}.[j] < w)
); last first.
    + auto => /> &1.
      do split; 2,3: by smt().
         * by rewrite size_nseq.
         * move => bitsL inL outL resultL resultR H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.
           split => [| /#].
           apply (eq_from_nth witness); first by rewrite H4 size_map size_to_list.
           rewrite H4 => i?.
           rewrite (nth_map witness). 
              - by rewrite size_to_list.
           rewrite get_to_list H9 //#.
if.
    + auto => /> &1 &2 *; smt(@W64).
    + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9. 
      do split; 1,2,11: by smt().
        * by rewrite size_put.
        * rewrite to_uintD /#.
        * rewrite to_uintD /#.
        * rewrite to_uintD /#.
        * rewrite to_uintD /#.
        * by rewrite logw_val.
        * rewrite logw_val /=/#.
        * rewrite to_uintD /#.
        * rewrite to_uintD_small 1:/# /= => j??.
          rewrite nth_put 1:/# get_setE //.
          case (j = to_uint out{1}) => [-> |?]; last first.
               - rewrite ifF 1:/# H7 //#.
          rewrite w_val ifT // log2_16 from_int_floor /= (: 15 = 2 ^ 4 - 1) 1:/# !and_mod //.
          rewrite (: 31 = 2 ^ 5 - 1) 1:/# !shr_div !of_uintK and_mod //=.
          smt(modz_small).
        * rewrite to_uintD_small 1:/# /= => j??.
          rewrite (: 31 = 2 ^ 5 - 1) 1:/# !and_mod // of_uintK.
          rewrite get_setE //.
          case (j = to_uint out{1}) => [?| /#].
          rewrite (: 15 = 2 ^ 4 - 1) 1:/# !and_mod // of_uintK.
          smt(modz_small).
    + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.
      do split; 1,2: by smt().
        * by rewrite size_put.
        * rewrite to_uintD /#.
        * rewrite to_uintD /#.
        * rewrite to_uintD /#.
        * rewrite to_uintD /#.
        * rewrite logw_val to_uintB // #smt:(@W64 pow2_3 modz_small).
        * rewrite logw_val H5 //= #smt:(@W64 pow2_32 modz_small @IntDiv).
        * rewrite H6 #smt:(@W64 pow2_32 @IntDiv).  
        * rewrite to_uintD_small 1:/# /= => j??.
          rewrite nth_put 1:/# get_setE //.
          case (j = to_uint out{1}) => [-> |?]; last first.
             - rewrite ifF 1:/# H7 //#.
          rewrite ifT // logw_val w_val /= (: 15 = 2^4 - 1) 1:/# (: 31 = 2^5 - 1) 1:/# !and_mod // !of_uintK //=.
          rewrite to_uint_shr.
             - rewrite !of_uintK /#.
          rewrite to_uint_shr.
             - rewrite !of_uintK /#.
         rewrite to_uint_truncateu8 to_uint_zeroextu32 !of_uintK /=. 
         smt(@IntDiv @W64 modz_small).
        * rewrite to_uintD_small 1:/# /= => j??. 
          rewrite (: 31 = 2^5 - 1) 1:/# (: 15 = 2^4 - 1) 1:/# !and_mod //=.        
          rewrite to_uint_shr.
             - rewrite !of_uintK /#.
          rewrite get_setE //.
          case (j = to_uint out{1}) => [?| /#].
          rewrite to_uint_zeroextu32 to_uint_truncateu8 !of_uintK #smt:(modz_small).
qed.

lemma wots_checksum_results (msg : W32.t Array64.t) :
    len1 = XMSS_WOTS_LEN1 /\  w = XMSS_WOTS_W =>
    equiv [
      M(Syscall).__csum ~ WOTS.checksum :
      (forall (k : int), 0 <= k < 64 => 0 <= to_uint msg.[k] <= w - 1) /\ 
      arg{1} = msg /\ arg{2} = map (W32.to_uint) (to_list msg) 
      ==>
      to_uint res{1} = res{2} /\
      0 <= res{2} <= len1 * (w - 1) 
    ].
proof.
rewrite /XMSS_WOTS_LEN1 /XMSS_WOTS_W => [#] len1_val w_val.
proc => /=.
while (
  #pre /\
  to_uint csum{1} = checksum{2} /\
  0 <= to_uint csum{1} <= (i{2} * (w - 1) * 2^8) /\
  i{2} = to_uint i{1} /\ 
  0 <= i{2} <= len1 /\
  m{2} = map (W32.to_uint) (to_list msg{1}) /\
  0 <= checksum{2} <= i{2} * (w - 1)
); last by auto => /> /#.
    + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6.
      do split; 5,6: by smt().
        * rewrite (nth_map witness); first by rewrite size_to_list /#.
          rewrite get_to_list w_val /= to_uintD to_uintB.
            - rewrite uleE of_uintK /= /#.
          rewrite of_uintK /= to_uint_zeroextu64 /#.
        * rewrite !to_uintD to_uintN to_uint_zeroextu64 of_uintK /= /#.
        * rewrite !to_uintD of_uintK /= to_uintN to_uint_zeroextu64 /#.
        * rewrite to_uintD /#.
        * rewrite (nth_map witness); first by rewrite size_to_list /#.
          rewrite get_to_list /#.
        * rewrite (nth_map witness); [by rewrite size_to_list /#|] => /#.
        * rewrite ultE of_uintK /= to_uintD /#.
        * rewrite ultE of_uintK to_uintD /#.
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
      0 <= to_uint (_start_ + _steps_) <= XMSS_WOTS_W - 1 /\
      to_uint _start_ < to_uint _start_ + to_uint _steps_
      ==> 
      val res{2} = to_list res{1}.`1 /\
      sub res{1}.`2 0 6 = sub _addr_ 0 6 /\
      res{1}.`2.[7] = W32.one /\
      res{1}.`2.[6] = _start_ + _steps_ - W32.one
    ].
proof. 
rewrite /XMSS_N /XMSS_WOTS_W.
move => [#] n_val w_val????. 
proc => //=.
swap {1} 1 2.
 
seq 2 1 : ( 
  0 <= to_uint start{1} <= w - 1/\
  0 <= to_uint steps{1} <= w - 1 /\
  0 <= to_uint (start{1} + steps{1}) <= w - 1 /\
  to_uint start{1} < to_uint start{1} + to_uint steps{1} /\
 
  address{2} = addr{1} /\
  val t{2} = to_list out{1} /\
  i{2} = to_uint start{1} /\
  s{2} = to_uint steps{1} /\
  val _seed{2} = to_list pub_seed{1} /\
  val t{2} = to_list out{1} /\  
  t{1} = start{1} + steps{1} /\
  addr{1} = _addr_
).
    + auto => /> *. 
      rewrite w_val.
      do 3! (split => [/# |]); do split; by rewrite NBytes.insubdK /P // size_to_list n_val.

sp 1 1.

unroll {1} 1; unroll {2} 1.
rcondt {2} 1; first by auto => /> /#. 
rcondt {1} 1; first by auto => /> &hr *; rewrite ultE to_uintD /#.

seq 2 2 : (
    #{/~addr{1} = _addr_}pre /\
    addr{1}.[6] = i{1}
); first by inline {1}; auto.

outline {2} [1-6] { (t, address) <@ ThashF.thash_f (t, _seed, address); }.


seq 1 1 : (#pre /\ to_list out{1} = val t{2} /\ addr{1}.[7] = W32.one).
    + inline M(Syscall).__thash_f_ M(Syscall)._thash_f; wp; sp.
      exists * out1{1}, pub_seed1{1}, addr{1}.
      elim * => P0 P1 P2.
      call (thash_f_equiv P0 P1 P2) => [/# |].
      auto => /> &1 &2 *.
      do split => //=; 1,2: by smt(@NBytes).
      move => *.
      do split; 1..3: by smt().
      smt(sub_k).
      
seq 1 1 : (
  #{/~chain_count{2} = 0}
   {/~i{1} = start{1}}
   {/~addr{1}.[6] = i{1}}pre /\
   i{1} = start{1} + W32.one /\
   chain_count{2} = to_uint start{1} + to_uint i{1}  
).


(* 
while ( 
  ((0 < chain_count{2}) => addr{1}.[6] = i{1}) /\
  sub addr{1} 0 6 = sub _addr_ 0 6 /\
  val t{2} = to_list out{1} /\
  0 <= to_uint start{1} <= w - 1/\
  0 <= to_uint steps{1} <= w - 1 /\ 
  0 <= to_uint (start{1} + steps{1}) <= w - 1 /\
  to_uint start{1} <= to_uint start{1} + to_uint steps{1} /\
  address{2} = addr{1} /\ 
  to_uint start{1} < to_uint i{1} <= to_uint start{1} + to_uint steps{1} /\
  t{1} = start{1} + steps{1} /\
  to_uint i{1} = i{2} + chain_count{2} /\
  0 <= chain_count{2} <= s{2} 
);  first by admit.
    + auto => /> &1 &2 *.
      rewrite !ultE to_uintD.
      do split => //=.
 



      do split; 1..3: by smt().
      move => addrL iL outL chaincountR t.
      rewrite ultE -!lezNgt => ????? *.
      split => [/# |].
      admit.
 
seq 2 2 : #pre; last by admit.
    + inline {1}; auto => &1 &2. 
      rewrite ultE.
      move => [#] H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 addrL *.
      do split => //. (* => // reduces the number of subgoals from 19 to 3 *)
       - move => ?.
         rewrite /addrL !get_setE //=.
       - apply (eq_from_nth witness); first by rewrite !size_sub. 
         rewrite size_sub // => j?.
         by rewrite -H2 !nth_sub //= /addrL !get_setE //= ifF 1:/# ifF 1:/#.
       - rewrite tP => j?.
         rewrite /set_key_and_mask /set_hash_addr /addrL !get_setE //. 
         case (j = 7) => //?.
         case (j = 6) => ?; first by rewrite -H15 to_uintK.
         smt(sub_k).
       







unroll {1} 1; rcondt {1} 1.
    + auto => /> &hr *. 
      by rewrite ultE to_uintD_small 1:/#. 




unroll {2} 1; rcondt {2} 1; first by auto => /> /#. 

seq 2 2 : (#{/~addr{1} = _addr_}pre); first by inline {1}; auto.
      
seq 1 6 : (
  #pre /\
  to_list out{1} = val t{2} /\
  sub addr{1} 0 6 = sub address{2} 0 6
).
    + inline M(Syscall).__thash_f_ M(Syscall)._thash_f.

admit.

while (
  (to_uint start{2} < to_uint i{1}
); first by admit.
*)
admit.
admit.

qed.


lemma expand_seed_correct (_in_seed _pub_seed : W8.t Array32.t) (a1 a2 : W32.t Array8.t):
    len = XMSS_WOTS_LEN /\ 
    n = XMSS_N /\ 
    prf_padding_val = XMSS_HASH_PADDING_PRF /\
    prf_kg_padding_val = XMSS_HASH_PADDING_PRF_KEYGEN /\
    padding_len = XMSS_PADDING_LEN =>
    equiv [
      M(Syscall).__expand_seed ~ WOTS.pseudorandom_genSK :
      
      arg{1}.`2 = _in_seed /\ 
      arg{1}.`3 = _pub_seed /\
      arg{1}.`4 = a1 /\

      arg{2}.`1 = NBytes.insubd (to_list _in_seed) /\
      arg{2}.`2 = NBytes.insubd(to_list _pub_seed) /\
      arg{2}.`3 = a2 /\ 

      sub a1 0 5 = sub a2 0 5
      ==>
      res{1}.`1 = DecodeWotsSk res{2} /\
      sub res{1}.`2 0 5 = sub a1 0 5
    ].
proof.
rewrite /XMSS_N  => [#] len_val n_val ???.
proc => /=.
conseq (: _ ==> 
  size sk{2} = len /\
  (forall (k : int), 0 <= k < 2144 => outseeds{1}.[k] = nth witness (nbytes_flatten sk{2}) k) /\
  sub addr{1} 0 5 = sub a1 0 5
).
  + auto => /> H0 addrL outseedsL skR H1 H2 H3.
    rewrite /DecodeWotsSk tP => j?. 
    by rewrite get_of_list //= insubdK /P // H2.

seq 5 3 : (
  val sk_seed{2} = to_list inseed{1} /\
  val seed{2} = to_list pub_seed{1} /\
  size sk{2} = len /\ 
  size (nbytes_flatten sk{2}) = len * n /\
  sub addr{1} 0 5 = sub a1 0 5 /\
  forall (k : int), 0 <= k < 8 => (k <> 5) => addr{1}.[k] = address{2}.[k]
).
    + inline{1}.
      auto => /> H0.  
      do split; 1,2: by rewrite NBytes.insubdK //= /P size_to_list n_val.
        * rewrite size_nseq /#.
        * rewrite size_nbytes_flatten size_nseq /#.
        * apply (eq_from_nth witness); first by rewrite !size_sub.
          rewrite size_sub // => i?.
          rewrite !nth_sub //= !get_setE /#.
        * rewrite /set_key_and_mask /set_hash_addr => k???.
          rewrite !get_setE //.
          case (k = 7) => //?.
          case (k = 6) => //?.
          smt(sub_k).

seq 1 0 : (#pre /\ sub buf{1} 0 n = to_list pub_seed{1}).
    + auto => /> &1 &2 H0 H1 H2 H3 H4 H5.
      apply (eq_from_nth witness); first by rewrite n_val size_sub // size_to_list.
      rewrite n_val size_sub // => j?.
      rewrite get_to_list nth_sub // initiE 1:/# /= ifT // initiE // /get8 /init32 /= initiE // /= /copy_32 initiE 1:/# /=.
      rewrite get32E pack4E /= wordP => k?.
      rewrite bits8E initiE //= initiE 1:/# /= initiE /= 1:/#.
      rewrite /init8 initiE /#.

seq 0 0 : (#pre /\ forall (k : int), 0 <= k < 32 => buf{1}.[k] = pub_seed{1}.[k]).
    + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 k??.
      have ->: buf{1}.[k] = nth witness (sub buf{1} 0 n) k by rewrite nth_sub /#.
      by rewrite H6 get_to_list.

while (
  len{2} = 67 /\
  size sk{2} = len /\ 
  ={i} /\ 0 <= i{2} <= 67 /\ 
  val sk_seed{2} = to_list inseed{1} /\
  val seed{2} = to_list pub_seed{1} /\
  sub addr{1} 0 5 = sub a1 0 5 /\
  (forall (k : int), 0 <= k < 32 => buf{1}.[k] = pub_seed{1}.[k]) /\
  (forall (k : int), 0 <= k < 32 * i{2} => outseeds{1}.[k] = nth witness (nbytes_flatten sk{2}) k) /\
  (forall (k : int), 0 <= k < 8 => (k <> 5) => addr{1}.[k] = address{2}.[k])
); last by auto => /> /#.

seq 1 1 : (
    #{/~forall (k : int),
     0 <= k && k < 8 => k <> 5 => addr{1}.[k] = address{2}.[k]}pre /\ 
    addr{1} = address{2}
).
    + inline {1}; auto => /> &1 &2 ???????? ?H??.
      split.
         * apply (eq_from_nth witness); first by rewrite !size_sub.
           rewrite size_sub // => j?.
           rewrite !nth_sub //= !get_setE 1:/# ifF 1:/#. 
           smt(sub_k).
         * rewrite tP => k*.
           rewrite /set_chain_addr.
           case (k = 5) => [->|?] //.
           by rewrite !get_setE // !ifF // H.

seq 2 1 : (#pre /\ val addr_bytes{2} = to_list addr_bytes{1}).
    + ecall {1} (addr_to_bytes_correctness addr{1}).
      by auto => /> ??????????????->.

seq 1 0 : (#pre /\ (forall (k : int), 0 <= k < 32 => buf{1}.[32 + k] = addr_bytes{1}.[k])).
    + auto => /> &1 &2 *. 
      do split => *; rewrite initiE 1:/# /=; [rewrite ifF | rewrite ifT] => /#.

seq 0 0 : ( (* cant use #pre in conseq *)
  #pre /\ 
  to_list buf{1} = (val seed{2} ++ val addr_bytes{2})
).
    + skip => /> &1 &2 ????? H ????? H1 *. 
      apply (eq_from_nth witness); [by rewrite size_cat H !size_to_list valP n_val |].
      rewrite size_to_list => j Hj.
      rewrite get_to_list.
      case (0 <= j < 32) => *.
        * rewrite nth_cat H size_to_list ifT 1:/# get_to_list /#.
      rewrite nth_cat H size_to_list ifF 1:/# H1 get_to_list /#. 

seq 2 1 : (#pre /\ val sk_i{2} = to_list ith_seed{1}).
    + inline {1} M(Syscall).__prf_keygen_ M(Syscall)._prf_keygen; wp; sp.
      exists * in_00{1}, key0{1}; elim * => _P1 _P2.
      call {1} (prf_keygen_correctness _P1 _P2) => [/# |].
      auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 -> *. 
      split => //. (* The first goal is trivial *)
      rewrite -H4 #smt:(@NBytes).  

auto => /> &1 &2  ? sizeSK ??? H0 H1 H2 H3 H4 H5 H6 H7 H8 H9. 
do split; 2,3,5,6:smt(); [by rewrite size_put sizeSK |]. 
move => k Hk0 Hk1; rewrite initE ifT 1:/#; auto => />. 
case (i{2} * 32 <= k && k < i{2} * 32 + 32) => *.
    + rewrite nth_nbytes_flatten; first by rewrite size_put /#.
      rewrite nth_put 1:/#.
      rewrite ifT 1:/# H9 get_to_list /#.
    + rewrite nth_nbytes_flatten; first by rewrite size_put /#.
      rewrite nth_put 1:/#.
      rewrite ifF 1:/#.
      rewrite -nth_nbytes_flatten 1:/#. 
      apply H3 => /#.
qed.

lemma pkgen_correct (_seed_ _pub_seed_ : W8.t Array32.t) (a1 a2 : W32.t Array8.t):
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
      arg{1}.`4 = a1 /\

      arg{2}.`1 = NBytes.insubd (to_list _seed_) /\
      arg{2}.`2 = NBytes.insubd (to_list _pub_seed_) /\
      arg{2}.`3 = a2 /\

      sub a1 0 5 = sub a2 0 5
      ==>
      res{1}.`1 = DecodeWotsPk res{2} /\
      sub res{1}.`2 0 5 = sub a1 0 5
    ]. 
proof.
rewrite /XMSS_N /XMSS_WOTS_LEN /XMSS_WOTS_W  => [#] w_val len_val n_val *.
proc => /=. 
seq 1 1 : (#pre /\ size pk{2} = len); first by auto => />; rewrite size_nseq /#.
swap {2} 1 1.
seq 1 1: (   
  val sk_seed{2} = to_list seed{1} /\
  val _seed{2} = to_list pub_seed{1} /\
  pk{1} = DecodeWotsSk wots_skey{2} /\
  size pk{2} = len /\
  sub a1 0 5 = sub a2 0 5 /\
  sub addr{1} 0 5 = sub address{2} 0 5 /\
  sub addr{1} 0 5 = sub a1 0 5 
).
    + inline {1} M(Syscall).__expand_seed_ M(Syscall)._expand_seed. 
      wp; sp.
      exists * inseed0{1}, pub_seed1{1}, addr1{1}, address{2}; elim * => _P1 _P2 _P3 _P4.
      call (expand_seed_correct _P1 _P2 _P3 _P4) => [/# |]. 
      skip => /> &1 &2 *; do split; [| | smt()]; by rewrite insubdK // /P size_to_list n_val.
     
conseq (: _ ==> 
  size pk{2} = len /\
  sub addr{1} 0 5 = sub a1 0 5 /\
  forall (k : int), 0 <= k < 2144 => pk{1}.[k] = nth witness (nbytes_flatten pk{2}) k
). 
    + auto => /> &1 &2 ??????????*.
      rewrite /DecodeWotsPk tP => j Hj.
      rewrite /of_list initE ifT //=. 
      by rewrite insubdK /#.
 
conseq /> => [/# |].
while (
  val sk_seed{2} = to_list seed{1} /\ 
  val _seed{2} = to_list pub_seed{1} /\
  sub address{2} 0 5 = sub addr{1} 0 5 /\

  size pk{2} = len /\
  ={i} /\ 
  0 <= i{1} <= 67 /\

  sub addr{1} 0 5 = sub a1 0 5 /\

  (forall (k : int), 0 <= k < 32 * i{1} => pk{1}.[k] = nth witness (nbytes_flatten pk{2}) k) /\
  (forall (k : int), 32 * i{1} <= k < 2144 => pk{1}.[k] = nth witness (nbytes_flatten (val wots_skey{2})) k)
); last first.
    + auto => /> &1 &2 H0 H1 H2 H3 H4 H5.
      do split; 1,2,4,5: by smt().
      by move => k ??; rewrite /DecodeWotsSk get_of_list.


seq 2 1 : (#pre /\ sub address{2} 0 6 = sub addr{1} 0 6).
    + inline {1}; auto => /> &1 &2 *.
      rewrite /set_chain_addr.
      do split; (
         apply (eq_from_nth witness); [by rewrite !size_sub | rewrite size_sub // => j?];
         rewrite !nth_sub //= !get_setE //=
      ).
        * rewrite ifF 1:/# ifF 1:/#; smt(sub_k).
        * rewrite ifF 1:/#; smt(sub_k).
        * case (j = 5) => //; smt(sub_k).

seq 2 2 : (#pre /\ to_list t{1} = val pk_i{2}).
    + inline M(Syscall).__gen_chain_inplace_ M(Syscall)._gen_chain_inplace; wp; sp.  
      exists * out0{1}, start0{1}, steps0{1}, addr1{1}, pub_seed1{1}.  
      elim * => _P1 _P2 _P3 _P4 _P5.  
      auto => />.   
      call (gen_chain_inplace_correct _P1 _P2 _P3 _P4 _P5) => [/# |].
      skip => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 *.   
      do split. 
          * apply nbytes_eq.
            rewrite insubdK; [by rewrite /P size_to_list n_val |].
            apply (eq_from_nth witness); first by rewrite valP n_val size_to_list.
            rewrite valP n_val => j?.
            rewrite get_to_list initiE // => />.
            rewrite /nbytes_flatten in H6.
            rewrite H8 1:/#.
            rewrite (nth_flatten witness 32).
                - pose P := (fun (s : W8.t list) => size s = 32).
                  pose L := (map NBytes.val (val wots_skey{2})).
                  rewrite -(all_nthP P L witness) /P /L size_map LenNBytes.valP len_val => k Hk.
                  rewrite (nth_map witness); [by rewrite LenNBytes.valP len_val |].  
                  by rewrite NBytes.valP n_val.
            rewrite (nth_map witness) 2:/#. 
            split => [/# | ?]. 
            rewrite LenNBytes.valP /#. 
          * by rewrite w_val.
          * rewrite -H1 #smt:(@NBytes).  
          * admit. (* Isto nao e por causa do gen chain ==> falta provas que os ultimos dois indices do address sao iguais *)

          * move => ????????H???.
            do split; 1..3: smt(sub_N). 
            by rewrite H.

auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12*; do split;2,3,6,7:smt(). 
    + rewrite size_put /#.
    + move => k Hk0 Hk1. 
      rewrite initE ifT 1:/# => />. 
      case (i{2} * 32 <= k && k < i{2} * 32 + 32) => *. 
          * rewrite nth_nbytes_flatten; first by rewrite size_put /#.
            rewrite nth_put 1:/# ifT 1:/# -H12 get_to_list /#.
          * rewrite nth_nbytes_flatten; first by rewrite size_put /#.
            rewrite nth_put 1:/# ifF 1:/#.
            rewrite H7 1:/# nth_nbytes_flatten /#.
    + smt(initiE).
qed.

(*** Pk From Sig : Doing ***)

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

      arg{2}.`1 = NBytes.insubd (to_list _msg_) /\
      arg{2}.`2 = EncodeWotsSignature (load_sig mem _sig_ptr_) /\
      arg{2}.`3 = NBytes.insubd (to_list _pub_seed_) /\
      arg{2}.`4 = _addr_ /\

      Glob.mem{2} = mem
      ==>
      res{1}.`1 = DecodeWotsPk res{2}
    ].
proof.
rewrite /XMSS_N /XMSS_WOTS_LOG_W /XMSS_WOTS_W /XMSS_WOTS_LEN1 /XMSS_WOTS_LEN2 /XMSS_WOTS_LEN.
move => ? [#] n_val logw_val w_val len1_val len2_val len_val *.
proc; auto => />. 
conseq (: _ ==> 
  size tmp_pk{2} = len /\
  address{2} = addr{1} /\ 
  forall (k : int), 0 <= k < 2144 => pk{1}.[k] = nth witness (nbytes_flatten tmp_pk{2}) k
).
    + auto => /> pkL pkR ? H.
      rewrite /DecodeWotsPk.
      rewrite tP => j?.
      rewrite get_of_list // insubdK; [by rewrite /P /# | by rewrite H]. 
seq 1 1 : (
  sig_ptr{1} = _sig_ptr_ /\
  addr{1} = address{2} /\
  val M{2} = to_list msg{1} /\
  val _seed{2} = to_list pub_seed{1} /\
  sig{2} = EncodeWotsSignature (load_sig mem sig_ptr{1}) /\

  size tmp_pk{2} = 67 /\

  Glob.mem{1} = mem /\ Glob.mem{2} = mem /\
  valid_ptr_i sig_ptr{1} 2144
).
    + auto => />; do split.
         * by rewrite insubdK // /P n_val size_to_list.
         * by rewrite insubdK // /P n_val size_to_list.
         * by rewrite size_nseq len_val.
inline M(Syscall).__chain_lengths_ M(Syscall)._chain_lengths M(Syscall).__chain_lengths.

seq 11 0 : (#pre /\ lengths2{1} = lengths{1} /\ msg2{1} = msg{1}); first by auto.

seq 1 1 : (
  val M{2} = to_list msg{1} /\
  val _seed{2} = to_list pub_seed{1} /\
  address{2} = addr{1} /\

  sig{2} = EncodeWotsSignature (load_sig mem sig_ptr{1}) /\
  lengths2{1} = lengths{1} /\ 

  msg{2} = map (W32.to_uint) (to_list t0{1}) /\
  (forall (k : int), 0 <= k < 64 => 0 <= to_uint t0{1}.[k] < w) /\

  size tmp_pk{2} = 67 /\
  
  Glob.mem{1} = mem /\ Glob.mem{2} = mem /\
  valid_ptr_i sig_ptr{1} 2144
).
    + exists * msg2{1}; elim * => P; call (base_w_results_64 P) => //=.
      admit.
(*
      auto => /> *; do split.
         * rewrite /EncodeWotsSignature size_chunk //= size_to_list //.
         * rewrite /EncodeWotsSignature size_flatten sumzE BIA.big_map /(\o) //= -(StdBigop.Bigint.BIA.eq_big_seq (fun _ => 32)) 1:#smt:(@List @BitChunking).
           rewrite  big_constz count_predT size_chunk //= size_to_list //=.  
         * rewrite /EncodeWotsSignature => />; smt(@List @BitChunking).
         * by rewrite size_to_list. 
*)
(*
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
*)
qed.



(* ============================================================================================================ *)        
lemma wots_sign_seed_corect (_m _sk_seed _pub_seed : W8.t Array32.t, a : W32.t Array8.t) :
    n = XMSS_N /\
    floor (log2 w%r) = XMSS_WOTS_LOG_W /\ 
    w = XMSS_WOTS_W /\ 
    len1 = XMSS_WOTS_LEN1 /\
    len2 = XMSS_WOTS_LEN2 /\
    len = XMSS_WOTS_LEN /\ 
    prf_padding_val = XMSS_HASH_PADDING_PRF /\
    padding_len = XMSS_PADDING_LEN /\ 
    F_padding_val = XMSS_HASH_PADDING_F /\
    prf_kg_padding_val = XMSS_HASH_PADDING_PRF_KEYGEN =>
    equiv [
      M(Syscall).__wots_sign ~ WOTS.sign_seed :
      arg{1}.`2 = _m /\
      arg{1}.`3 = _sk_seed /\
      arg{1}.`4 = _pub_seed /\
      arg{1}.`5 = a /\

      arg{2}.`1 = to_list _m /\
      arg{2}.`2 = NBytes.insubd (to_list _sk_seed) /\
      arg{2}.`3 = NBytes.insubd (to_list _pub_seed) /\
      arg{2}.`4 = a
      (* Nao me interessa o valor de address no resultado pq 
         nao se usa mais o addr depois de chamar esta funcao 
       *)
      ==>
      res{2} = EncodeWotsSignature res{1}.`1
    ].
proof.
rewrite /XMSS_N /XMSS_WOTS_LOG_W /XMSS_WOTS_W /XMSS_WOTS_LEN /XMSS_WOTS_LEN1 /XMSS_WOTS_LEN2 => 
    [#] n_val logw_val w_val len1_val len2_val len_val *.
proc => /=.
conseq ( : 
  M{2} = to_list msg{1} /\
  val sk_seed{2} = to_list seed{1} /\  val pub_seed{2} = to_list pub_seed{1} /\
  address{2} = addr{1}
  ==>
  _
); first by auto => />; rewrite !insubdK // /P size_to_list n_val.
seq 1 1 : (#pre /\ size sig{2} = len); first by auto => /> *; rewrite size_nseq len_val.
swap {1} 2 -1.

seq 1 1 : (
  #{/~address{2} = addr{1}}pre /\
  sig{1} = DecodeWotsSk wots_skey{2} /\
  sub addr{1} 0 5 = sub address{2} 0 5
).
    + inline {1} M(Syscall).__expand_seed_ M(Syscall)._expand_seed.
      wp; sp.
      exists * inseed0{1}, pub_seed1{1}, addr1{1}, address{2}.
      elim * => P0 P1 P2 P3.
      call (expand_seed_correct P0 P1 P2 P3) => [// |].  
      skip => /> &2 <- <- *; smt(@NBytes).
 
seq 1 8 : (
    #pre /\ 
    map W32.to_uint (to_list lengths{1}) = msg{2} /\
    (forall (k : int), 0 <= k < 67 => 0 <= to_uint lengths{1}.[k] < w)
).
    + inline {1} M(Syscall).__chain_lengths_ M(Syscall)._chain_lengths.
      inline {1} M(Syscall).__chain_lengths.
      sp 10 0.
      seq 2 1 : (
          #{/~t0{1} = witness}pre /\ 
          msg{2} = map W32.to_uint (to_list t0{1}) /\
          forall (k : int), 0 <= k < 64 => 0 <= to_uint t0{1}.[k] < w
      ); first by exists * msg2{1}; elim * => P; call (base_w_results_64 P) => //=; auto => />.

      seq 1 0 : (#{/~lengths2{1} = lengths1{1}}pre /\ map W32.to_uint (sub lengths2{1} 0 64) = msg{2}).
        * auto => /> &1 &2 *.
          apply (eq_from_nth witness); first by rewrite !size_map.
          rewrite size_map size_sub // => i?.
          rewrite (nth_map witness); first by rewrite size_sub.
          rewrite nth_sub //= initiE 1:/# /= ifT // (nth_map witness); first by rewrite size_to_list.
          by rewrite get_to_list.
      
      wp; conseq /> => [/# |].

      inline {1} M(Syscall).__wots_checksum.
      seq 3 0 : (#{/~t1{1} = witness}pre /\ csum_base_w{1} = t1{1} /\ msg_base_w{1} = lengths2{1}); first by auto.
     
      seq 4 0 : ( 
         #pre /\
         (forall (k : int), 0 <= k < 64 => 0 <= to_uint buf{1}.[k] < w) /\
         msg{2} = map (W32.to_uint) (to_list buf{1})
      ).
          + auto => /> &1 &2 ?????H.
            split; last first.
               * apply (eq_from_nth witness); first by rewrite !size_map !size_iota.
                 rewrite size_map size_to_list => j?.
                 rewrite -H (nth_map witness); first by rewrite size_sub.
                 rewrite nth_sub //= (nth_map witness); first by rewrite size_to_list.
                 by rewrite get_to_list initiE.
               * move => j??. 
                 rewrite !initiE //.
                 have ->: to_uint lengths2{1}.[j] = nth witness (map W32.to_uint (sub lengths2{1} 0 64)) j.
                   + rewrite (nth_map witness); [by rewrite size_sub | by rewrite nth_sub].
                 rewrite H (nth_map witness); first by rewrite size_to_list.
                 rewrite get_to_list /#.

       seq 1 1 : (#pre /\ to_uint csum{1} = csum{2} /\ 0 <= csum{2} <= len1 * (w - 1)).
          + exists * buf{1}; elim * => P; call {1} (wots_checksum_results P) => //.
            skip => /> /#.

       seq 3 0 : (#pre /\ u{1} = W64.of_int 4); first by auto.
 
       seq 2 2 : (
           #{/~to_uint csum{1} = csum{2}}
            {/~u{1} = W64.of_int 4}pre /\ 
          to_uint csum{1} = to_uint csum_32{2}
       ).
          + auto => /> &1 &2 *.
            rewrite (: 63 = 2^6 - 1) 1:/# and_mod //=. 
            have ->: truncateu8 ((of_int 4))%W64 = W8.of_int 4 by smt(@W64 pow2_64).
            rewrite !shl_shlw //= len2_val w_val log2_16 /= from_int_ceil //=. 
            rewrite !to_uint_shl //= of_uintK //= #smt:(modz_small).

       seq 0 1 : (#pre /\ len_2_bytes{2} = 2).
          + auto => /> *. 
            rewrite w_val len2_val log2_16 -fromintM //= from_int_ceil //=.
            apply ceil_3_2.
      
       seq 1 1 : (#pre /\ to_list csum_bytes_p{1} = csum_bytes{2}).
          + exists * csum{1}, csum_32{2}.
            elim * => P0 P1.
            call {1} (ull_to_bytes2_post P0 P1).
            by auto.
  
       seq 1 1 : (#{/~csum_base_w{1} = t1{1}}pre /\ csum_base_w{2} = map W32.to_uint (to_list csum_base_w{1}) /\ 
                  forall (k : int), 0 <= k < size csum_base_w{2} => 0 <= nth witness csum_base_w{2} k < w).
          + wp.
            exists * csum_bytes_p{1}; elim * => P.
            call (base_w_results_3 P) => //=.
            auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 resultL H12 k0 H13. 
            rewrite size_map size_to_list =>  H14.
            rewrite (nth_map witness); first by rewrite size_to_list /#.
            rewrite get_to_list /#.
       
       auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.
       rewrite size_map size_to_list => H11 *.
       split; last first.
          * move => k??. 
            rewrite initiE //=. 
            case (64 <= k < 67) => H; last first.
                    * have ->: to_uint lengths2{1}.[k] = nth witness (map W32.to_uint (sub lengths2{1} 0 64)) k.
                           + rewrite (nth_map witness) /=; first by rewrite size_sub /#.
                             rewrite nth_sub /#.
                      rewrite H5 (nth_map witness); first by rewrite size_to_list /#.
                      rewrite get_to_list /#.
                    * have ->: to_uint csum_base_w{1}.[k - 64] = nth witness (map W32.to_uint (to_list csum_base_w{1})) (k - 64).
                           + rewrite (nth_map witness); first by rewrite size_to_list /#. 
                             rewrite get_to_list /#.
                      smt().

       apply (eq_from_nth witness); first by rewrite !size_map size_iota size_cat !size_map !size_iota /#.
       rewrite size_map size_to_list => j?.
       rewrite (nth_map witness); first by rewrite size_to_list /#.
       rewrite get_to_list initiE //=.
       case (64 <= j < 67) => H.
          * rewrite nth_cat size_map size_to_list ifF 1:/# (nth_map witness); first by rewrite size_to_list /#.
            rewrite get_to_list /#.
          * rewrite nth_cat size_map size_to_list ifT 1:/# (nth_map witness); first by rewrite size_to_list /#.
            rewrite get_to_list.
            have ->: to_uint lengths2{1}.[j] = nth witness (map W32.to_uint (sub lengths2{1} 0 64)) j.
               + rewrite (nth_map witness); first by rewrite size_sub /#.
                 rewrite nth_sub /#.
            rewrite H5 (nth_map witness); first by rewrite size_to_list /#.
            by rewrite get_to_list.

(* Invariante: Em cada iteracao escrevemos nbytes *)
(* A chave e inicialmente escrita no array sig e vai sendo sobreescrita ate no fim so estar la assinatura *)

while (
    0 <= i{1} <= 67 /\
    ={i} /\
    size sig{2} = len /\
    val sk_seed{2} = to_list seed{1} /\
    val pub_seed{2} = to_list pub_seed{1} /\
    M{2} = to_list msg{1} /\ 

    sub addr{1} 0 5 = sub address{2} 0 5 /\

    map W32.to_uint (to_list lengths{1}) = msg{2} /\
    (forall (k : int), 0 <= k < 67 => 0 <= to_uint lengths{1}.[k] < w) /\
   
   
    sub sig{1} 0 (32 * i{1}) = sub_list (nbytes_flatten sig{2}) 0 (32 * i{1}) /\
    sub sig{1} (32 * i{1}) (67*32 - 32*i{1}) = sub (DecodeWotsSk wots_skey{2}) (32 * i{1}) (67*32 - 32*i{1})
); last first.
    + auto => /> &1 &2 H0 H1 H2 H3 H4.
      do split; 2: by smt().
        - apply (eq_from_nth witness); first by rewrite size_sub // size_sub_list.
          rewrite size_sub // /#.
        - move => addrL sigL addrR iR sigR H5 H6 H7 H8 H9 H10 H11 H12.
          rewrite /EncodeWotsSignature.  
          congr.
          apply (eq_from_nth witness); first by rewrite H9 size_map size_chunk // size_to_list /#.
          rewrite H9 len_val => j?.
          rewrite (nth_map witness); first by rewrite size_chunk 1:/# size_to_list /#.
          apply nbytes_eq. 
          rewrite insubdK. 
              * rewrite /P /chunk nth_mkseq /=; first by rewrite size_to_list /#.
                rewrite size_take 1:/# size_drop 1:/# size_to_list /#.
          rewrite /chunk nth_mkseq /=; first by rewrite size_to_list.
          apply (eq_from_nth witness); first by rewrite valP size_take 1:/# size_drop 1:/# size_to_list /#.
          rewrite valP n_val => jj?.
          rewrite nth_take 1,2:/# nth_drop 1,2:/# get_to_list.
          have ->: sigL.[32*j + jj] = nth witness (sub sigL 0 (32 * iR)) (32*j + jj) by rewrite nth_sub // /#.
          rewrite H11 /sub_list nth_mkseq 1:/# /= nth_nbytes_flatten /#.

wp; conseq />.

seq 2 1 : (#pre /\ sub address{2} 0 6 = sub addr{1} 0 6).
    + inline {1}; auto => /> &1 &2 *.
      rewrite /set_chain_addr.
      split; (
          apply (eq_from_nth witness); [by rewrite !size_sub | rewrite size_sub // => j?];
          rewrite !nth_sub //= !get_setE //
      ).
         - rewrite ifF 1:/# ifF 1:/#; smt(sub_k).
         - case (j = 5) => //?; smt(sub_k).

inline {1} M(Syscall).__gen_chain_inplace_.
inline {1} M(Syscall)._gen_chain_inplace.
sp; wp.
exists * out0{1}, start0{1}, steps0{1}, addr1{1}, pub_seed1{1}.        
elim * => _P1 _P2 _P3 _P4 _P5. 
call (gen_chain_inplace_correct _P1 _P2 _P3 _P4 _P5) => [/# |].

skip => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.
do split.
          + apply nbytes_eq.
            rewrite insubdK /=; first by rewrite /P size_to_list /#.
            apply (eq_from_nth witness); first by rewrite valP size_to_list /#.
            rewrite valP n_val => j?.
            rewrite get_to_list /= initiE //=.
            have ->: sig{1}.[i{2} * 32 + j] = nth witness (sub sig{1} (32 * i{2}) (2144 - 32 * i{2})) j by rewrite nth_sub /#.
            rewrite H8 /DecodeWotsSk nth_sub 1:/# get_of_list 1:/# nth_nbytes_flatten 2:/# valP /#.
          + rewrite (nth_map witness); [by rewrite size_to_list | by rewrite get_to_list].
          + rewrite -H4 #smt:(@NBytes).
          + admit. (* Isto e falso ==> corrigir o gen chain inplace *) 
          + smt().
          + smt().
          + smt().
          + smt().        
          + move => H12 H13 H14 H15 H16 H17 H18 resultL resultR H19 *.
            do split.
               * smt().
               * smt().
               * smt(size_put).
               * admit. (* Falta isto no gen chain inplace *) 
               * apply (eq_from_nth witness); first by rewrite size_sub 1:/# size_sub_list /#.
                 rewrite size_sub 1:/# => j?.
                 rewrite nth_sub 1:/# initiE 1:/# /=.
                 rewrite /sub_list nth_mkseq 1:/# /= nth_nbytes_flatten; first by smt(size_put). 
                 rewrite nth_put 1:/#.
                 case (i{2} = j %/ n) => //H.
                    * rewrite ifT 1:/# -get_to_list -H19 /#.
                    * rewrite ifF 1:/#.
                      have ->: sig{1}.[j] = nth witness (sub sig{1} 0 (32 * i{2})) j by rewrite nth_sub /#.
                      rewrite H7 /sub_list nth_mkseq 1:/# /= nth_nbytes_flatten /#.
               * apply (eq_from_nth witness); first by rewrite !size_sub /#.
                 rewrite size_sub 1:/# => j?.
                 rewrite nth_sub 1:/# initiE 1:/# /=.
                 rewrite nth_sub 1:/# /DecodeWotsSk.
                 case (i{2} * 32 <= 32 * (i{2} + 1) + j && 32 * (i{2} + 1) + j < i{2} * 32 + 32) => //= H.
                    * rewrite get_of_list 1:/# nth_nbytes_flatten /#.
                    * rewrite get_of_list 1:/# nth_nbytes_flatten; first by rewrite valP /#.
                      have ->: sig{1}.[32 * (i{2} + 1) + j] = nth witness (sub sig{1} (32 * i{2}) (2144 - 32 * i{2})) (32 + j) by rewrite nth_sub /#.
                      rewrite H8 nth_sub 1:/# /DecodeWotsSk get_of_list 1:/# nth_nbytes_flatten 2:/# valP /#.
               * smt().
               * smt().
qed.

