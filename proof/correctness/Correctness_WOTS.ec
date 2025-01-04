pragma Goals : printall.

require import AllCore List RealExp IntDiv.

from Jasmin require import JModel JArray.

require import Params Address Hash BaseW WOTS. 

require import XMSS_IMPL Parameters.

require import Array2 Array3 Array8 Array32 Array64 Array67 Array96 Array2144.

require import WArray32.

require import Correctness_Bytes Correctness_Mem Correctness_Address Correctness_Hash. 
require import GenChainProof.
require import Repr2.
require import Utils2.

require import BitEncoding.
(*---*) import BitChunking.

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
      rewrite get_to_list nth_sub // initiE 1:/# /= ifT // initiE // /get8 /init32 /= initiE // /= /copy_32. 

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
      exists * out0{1}, start0{1}, steps0{1}, pub_seed1{1}, addr1{1}, address{2}.  
      elim * => _P1 _P2 _P3 _P4 _P5 _P6.  
      call (gen_chain_correct _P1 _P2 _P3 _P4 _P5 _P6) => [/# |].
      skip => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.   
      do split.
          * apply nbytes_eq.
            rewrite insubdK; [by rewrite /P size_to_list n_val |].
            apply (eq_from_nth witness); first by rewrite valP n_val size_to_list.
            rewrite valP n_val => j?.
            rewrite get_to_list initiE // => />.
            rewrite /nbytes_flatten in H6.
            rewrite H8 1:/#.
            rewrite nth_nbytes_flatten; first by rewrite valP /#.
            by do congr => /#. 
          * by rewrite w_val.
          * rewrite -H1 #smt:(@NBytes).  
          * smt().
          * by rewrite H11.
          * move => H12 H13 H14 H15 H16 H17 H18 resultL resultR -> H19.
            do split; smt(sub_N).

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
    + move => k??.
      rewrite nth_nbytes_flatten; first by rewrite valP /#.
      by rewrite initiE 1:/# /= ifF 1:/# H8 1:/# nth_nbytes_flatten // valP /#.
qed.

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
      
      valid_ptr_i _sig_ptr_ XMSS_WOTS_SIG_BYTES /\

      arg{1}.`2 = _sig_ptr_ /\
      arg{1}.`3 = _msg_ /\
      arg{1}.`4 = _pub_seed_ /\ 
      arg{1}.`5 = _addr_ /\ 
      Glob.mem{1} = mem /\

      arg{2}.`1 = NBytes.insubd (to_list _msg_) /\
      arg{2}.`2 = EncodeWotsSignature (load_sig mem _sig_ptr_) /\
      arg{2}.`3 = NBytes.insubd (to_list _pub_seed_) /\
      arg{2}.`4 = _addr_ 
      ==>
      res{1}.`1 = DecodeWotsPk res{2} /\
      Glob.mem{1} = mem (* The memory is not changed *)
    ].
proof.
rewrite /XMSS_N /XMSS_WOTS_LOG_W /XMSS_WOTS_W /XMSS_WOTS_LEN1 /XMSS_WOTS_LEN2 /XMSS_WOTS_LEN.
move => ? [#] n_val logw_val w_val len1_val len2_val len_val *.
proc => /=. 

conseq (: _ ==> 
  size tmp_pk{2} = len /\
  Glob.mem{1} = mem /\
  forall (k : int), 0 <= k < 2144 => pk{1}.[k] = nth witness (nbytes_flatten tmp_pk{2}) k
).
    + auto => /> H0 H1 pkL pkR ? H.
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

  Glob.mem{1} = mem /\
  valid_ptr_i sig_ptr{1} XMSS_WOTS_SIG_BYTES (* 2144 *)
).

    + auto => /> *; do split.
         * by rewrite insubdK // /P n_val size_to_list.
         * by rewrite insubdK // /P n_val size_to_list.
         * by rewrite size_nseq len_val.
   
seq 1 8 : (
    #pre /\ 
    map W32.to_uint (to_list lengths{1}) = msg{2} /\
    forall (k : int), 0 <= k < size msg{2} => 0 <= nth witness msg{2} k < w
).
(* A prova do chain lengths comeca aqui *)
    + inline M(Syscall).__chain_lengths_ M(Syscall)._chain_lengths M(Syscall).__chain_lengths.
      conseq /> => [/# |]; sp.
  
      seq 1 1 : (
            #{/~t0{1} = (init (fun (i0 : int) => lengths2{1}.[0 + i0]))%Array64}pre /\ 
            map W32.to_uint (to_list t0{1}) = msg{2} /\
            size msg{2} = 64 /\
            forall (k : int), 0 <= k < 64 => 0 <= nth witness msg{2} k < w
      ).
        * exists * msg2{1}; elim * => P0.
          call {1} (base_w_results_64 P0) => [/# |].
          auto => /> *.
          rewrite size_map size_to_list; split => // k??.
          rewrite (nth_map witness); first by rewrite size_to_list.
          rewrite get_to_list /#.       

      seq 1 0 : (#{/~lengths2{1} = lengths1{1}}pre /\ sub lengths2{1} 0 64 = to_list t0{1}).
        * auto => /> &1 &2 *.
          apply (eq_from_nth witness); first by rewrite size_sub // size_to_list.
          rewrite size_sub // => j?.
          by rewrite nth_sub // initiE 1:/# /= ifT. 
          
      seq 1 0 : (#{/~t1{1} = witness}pre /\ to_list t1{1} = sub lengths2{1} 64 3).
        * auto => /> *.
          apply (eq_from_nth witness); first by rewrite size_to_list size_sub.
          rewrite size_to_list => j?.
          by rewrite get_to_list /= initiE //= nth_sub. 
 
      inline M(Syscall).__wots_checksum.

      sp.
 
      seq 1 1 :(#pre /\ W64.to_uint csum{1} = csum{2} /\ 0 <= csum{2} <= len1 * (w - 1)).
        * exists * buf{1}; elim * => P; auto.
          call {1} (wots_checksum_results P) => [/# |].
          skip => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8.
          have E6 : forall (k : int), 0 <= k < 64 => 0 <= to_uint t0{1}.[k] < w.
               + move => j?.  
                 have ->: to_uint t0{1}.[j] = nth witness (map W32.to_uint (to_list t0{1})) j by rewrite (nth_map witness); [by rewrite size_to_list | by rewrite get_to_list].
                 by apply H6.
          split.
            - move => k??. 
              rewrite !initiE //=. 
              have ->: to_uint lengths2{1}.[k] = nth witness (map W32.to_uint (to_list t0{1})) k. 
               + rewrite -H7 (nth_map witness); first by rewrite size_sub.
                 by rewrite nth_sub.
              smt().
            - do congr.
              rewrite tP => j?.
              rewrite !initiE //=.
              rewrite (: t0{1}.[j] = nth witness (to_list t0{1}) j); first by rewrite get_to_list.
              by rewrite -H7 nth_sub.
              
     seq 4 2 : (
          #{/~W64.to_uint csum{1} = csum{2}}pre /\ 
          to_uint csum{1} = to_uint csum_32{2} /\
          0 <= to_uint csum_32{2} < W32.max_uint
     ).
        * auto => /> &1 &2 *.
          rewrite w_val.
          rewrite (: 63 = 2^6 - 1) 1:/# and_mod //=. 
          have ->: truncateu8 ((of_int 4))%W64 = W8.of_int 4 by smt(@W64 pow2_64).
          rewrite !shl_shlw //= len2_val.
            - by have ->: floor (log2 16%r) = 4 by rewrite log2_16 from_int_floor.
          have ->: floor (log2 16%r) = 4 by rewrite log2_16 from_int_floor.
          simplify.
          rewrite !to_uint_shl //= of_uintK //=.
          have ->: to_uint csum{1} %% 4294967296 = to_uint csum{1} by smt(@W64 pow2_64 @IntDiv).
          smt(modz_small).

     seq 0 1 : (#pre /\ len_2_bytes{2} = 2).
        * auto => /> *. 
          by rewrite w_val len2_val log2_16 -fromintM //= from_int_ceil //=; apply ceil_3_2.
  
     seq 2 1 : (
          #{/~csum_bytes_p{1} = witness}pre /\ 
          to_list csum_bytes_p{1} = csum_bytes{2}
     ).
        * sp.  
          exists * csum{1}, csum_32{2}; elim * => P0 P1; auto.
          by ecall {1} (ull_to_bytes2_post P0 P1); auto.

     seq 1 1 : (
          #{/~csum_base_w{1} = t1{1}}pre /\ 
          map W32.to_uint (to_list csum_base_w{1}) = csum_base_w{2} /\
          forall (k : int), 0 <= k < 3 => 0 <= nth witness csum_base_w{2} k < w
      ).
        * exists * csum_bytes_p{1}; elim * => P0.
          call {1} (base_w_results_3 P0) => [/# |].
          auto => /> *.  
          by rewrite (nth_map witness); [by rewrite size_to_list | by rewrite get_to_list /#].
 
     auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 *.
     have E6: forall (k : int), 0 <= k < 64 => 0 <= to_uint t0{1}.[k] < w.
        * move => k?.
          have ->: to_uint t0{1}.[k] = nth witness (map W32.to_uint (to_list t0{1})) k by rewrite (nth_map witness); [by rewrite size_to_list | by rewrite get_to_list].
          by apply H6.

     split.     
        * apply (eq_from_nth witness); first by rewrite size_cat !size_map !size_iota /#.
          rewrite size_map size_to_list => j?.
          case (0 <= j < 64) => H.
            * rewrite nth_cat size_map size_to_list ifT 1:/# (nth_map witness); first by rewrite size_to_list.
              rewrite get_to_list /= initiE //= ifF 1:/# -H7 (nth_map witness); first by rewrite size_sub.
              by rewrite nth_sub.
            * rewrite nth_cat size_map size_to_list ifF 1:/# !(nth_map witness).
                - by rewrite size_to_list.
                - by rewrite size_iota.
                - by rewrite size_to_list /#.
                - by rewrite size_iota /#.
              rewrite /= initiE; first by rewrite nth_iota.
              rewrite /= ifT; first by rewrite nth_iota /#.
              rewrite !nth_iota // /#.
        * rewrite size_cat !size_map !size_iota (: max 0 64 + max 0 3 = 67) 1:/# => k??.
          case (0 <= k < 64) => H.
            * rewrite nth_cat size_map size_to_list ifT 1:/# (nth_map witness); first by rewrite size_to_list.
              rewrite get_to_list /= /#. 
            * rewrite nth_cat size_map size_to_list ifF 1:/# (nth_map witness); first by rewrite size_to_list /#.
              rewrite get_to_list /=.
              have ->: to_uint csum_base_w{1}.[k - 64] = nth witness (map W32.to_uint (to_list csum_base_w{1})) (k - 64).
                - rewrite (nth_map witness); first by rewrite size_to_list /#.
                  by rewrite get_to_list.
              smt().

(* A prova do chain lengths acaba aqui *)
    
while (
  0 <= i{1} <= len /\
  ={i} /\
  sub addr{1} 0 6 = sub address{2} 0 6 /\
  map W32.to_uint (to_list lengths{1}) = msg{2} /\
  sig_ptr{1} = _sig_ptr_ /\ 
  val M{2} = to_list msg{1} /\
  val _seed{2} = to_list pub_seed{1} /\
  sig{2} = EncodeWotsSignature (load_sig mem sig_ptr{1}) /\
  size tmp_pk{2} = 67 /\
  Glob.mem{1} = mem /\ 
  valid_ptr_i sig_ptr{1} XMSS_WOTS_SIG_BYTES /\
  map W32.to_uint (to_list lengths{1}) = msg{2} /\
  sub pk{1} 0 (32 * i{1}) = sub_list (nbytes_flatten tmp_pk{2}) 0 (32 * i{1}) /\
  forall (k : int), 0 <= k < size msg{2} => 0 <= nth witness msg{2} k < w 
); last first.

(* === last subgoal of while starts here === *)

auto => /> &1 &2 H0 H1 H2 H3 H4 H5.
do split; 1,3: by smt().
 - apply (eq_from_nth witness); [by rewrite size_sub // size_sub_list | rewrite size_sub /#].
 - move => addrL pkL addrR iR tmpPkR ????.
   have ->: iR = 67 by smt().
   move => H6 H7 H8.
   split => [/# |]. 
   move => k??.
   have ->: pkL.[k] = nth witness (sub pkL 0 (32 * 67)) k by rewrite nth_sub /#.
   by rewrite H8 /sub_list nth_mkseq.
(* === last subgoal of while ends here === *)

    + seq 2 1 : #pre.
         * inline {1}; auto => /> *.
           apply (eq_from_nth witness); first by rewrite !size_sub.
           rewrite size_sub // => j?.
           rewrite !nth_sub // /set_chain_addr /=.
           rewrite !get_setE //.
           by case (j = 5) => //?; smt(sub_k). 

    + seq 1 1 : (#pre /\ to_uint start{1} = msg_i{2} /\ start{1} = lengths{1}.[i{1}]).
         * auto => /> &1 &2.
           move => H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 *.
           rewrite (nth_map witness); [by rewrite size_to_list | by rewrite get_to_list].

    + seq 2 0 : (#pre /\ to_uint steps{1} = w - 1 - msg_i{2}).
         * auto => /> &1 &2.
           rewrite w_val size_map size_to_list => H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 *.
           rewrite to_uintB.
              - rewrite uleE of_uintK /=. 
                have ->: to_uint lengths{1}.[i{2}] = nth witness (map W32.to_uint (to_list lengths{1})) i{2}; last by smt().
                rewrite (nth_map witness); first by rewrite size_to_list.
                by rewrite get_to_list.           
           by rewrite of_uintK /=.
    + seq 2 0 : (#pre /\ to_uint t{1} = to_uint _sig_ptr_ + 32 * i{1}); first by auto => /> *; smt(@W64 pow2_64).     

    + seq 1 1 : (#pre /\ to_list aux_0{1} = val sig_i{2}).
         * ecall {1} (p_memcpy_ptr_correct t{1}).
           auto => /> &1 &2 *; do split; 1..3: by smt().
           move => ???.
           apply (eq_from_nth witness); first by rewrite valP size_to_list n_val.
           rewrite size_to_list => j?.
           rewrite get_to_list initiE //=.
           rewrite /EncodeWotsSignature /load_sig.
           rewrite insubdK.
              - rewrite /P size_map size_chunk // size_to_list /#. 
           rewrite (nth_map witness); first by rewrite size_chunk // size_to_list /#.
           rewrite insubdK.
              - rewrite /P /chunk nth_mkseq /=; first by rewrite size_to_list /#.
                rewrite size_take // size_drop 1:/# size_to_list /#. 
           rewrite /chunk nth_mkseq.
              - rewrite size_to_list /#.           
           rewrite /= nth_take // 1:/# nth_drop 1,2:/# get_to_list initiE 1:/# /=.
           congr => /#.

    + conseq />.
      inline {1} M(Syscall).__gen_chain_inplace_ M(Syscall)._gen_chain_inplace. 
      sp; wp.
      exists * out0{1}, start1{1}, steps1{1}, pub_seed1{1}, addr1{1}, address{2}.
      elim * => P0 P1 P2 P3 P4 P5; auto.
      call (gen_chain_correct P0 P1 P2 P3 P4 P5) => [/# |].
      auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 *.
      rewrite size_map size_to_list in H9.
      do split.
         - apply nbytes_eq; apply (eq_from_nth witness); first by rewrite !valP.
           rewrite valP n_val => j?.
           rewrite insubdK; first by rewrite /P size_to_list n_val.
           rewrite get_to_list initiE // /= initiE 1:/# /= ifT 1:/# -get_to_list H14.
           do congr => /#. 
         - smt().
         - rewrite -H4; smt(@NBytes). 
         - have ->: to_uint lengths{1}.[i{2}] = nth witness (map W32.to_uint (to_list lengths{1})) i{2} by rewrite (nth_map witness); [by rewrite size_to_list | by rewrite get_to_list].    
           smt().
         - have ->: to_uint lengths{1}.[i{2}] = nth witness (map W32.to_uint (to_list lengths{1})) i{2} by rewrite (nth_map witness); [by rewrite size_to_list | by rewrite get_to_list].
           smt().
         - rewrite H12. 
           have ->: to_uint lengths{1}.[i{2}] = nth witness (map W32.to_uint (to_list lengths{1})) i{2} by rewrite (nth_map witness); [by rewrite size_to_list | by rewrite get_to_list].
           smt().
         - rewrite H12. 
           have ->: to_uint lengths{1}.[i{2}] = nth witness (map W32.to_uint (to_list lengths{1})) i{2} by rewrite (nth_map witness); [by rewrite size_to_list | by rewrite get_to_list].
           smt().
         - rewrite to_uintD H12. 
           have ->: to_uint lengths{1}.[i{2}] = nth witness (map W32.to_uint (to_list lengths{1})) i{2} by rewrite (nth_map witness); [by rewrite size_to_list | by rewrite get_to_list].
           smt().
         - rewrite to_uintD H12. 
           have ->: to_uint lengths{1}.[i{2}] = nth witness (map W32.to_uint (to_list lengths{1})) i{2} by rewrite (nth_map witness); [by rewrite size_to_list | by rewrite get_to_list].
           smt().
         - move => H15 H16 H17 H18 H19 H20 H21 H22 H23 resL resR H24 H25.

           rewrite size_put.
           do split; 1..4,6,7: by smt().
           apply (eq_from_nth witness); first by rewrite size_sub 1:/# size_sub_list // /#.
           rewrite size_sub 1:/# => j?.
           rewrite nth_sub 1:/# initiE 1:/# /= /sub_list nth_mkseq //= nth_nbytes_flatten; first by rewrite size_put /#.
           rewrite nth_put 1:/#.
           case (i{2} = j %/ n) => H.
              * rewrite ifT 1:/# H24 get_to_list /#.
              * rewrite ifF 1:/# /= initiE 1:/# /= ifF 1:/#.
                have ->: pk_L.[j] = nth witness (sub pk_L 0 (32 * i{2})) j by rewrite nth_sub /#.
                rewrite H8 /sub_list nth_mkseq 1:/# /= nth_nbytes_flatten // /#.
qed. 

(* ============================================================================================================ *)      

lemma wots_sign_seed_addr (_m _sk_seed _pub_seed : W8.t Array32.t)
                          (a1 a2 : W32.t Array8.t) :
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
      arg{1}.`5 = a1 /\

      arg{2}.`1 = to_list _m /\
      arg{2}.`2 = NBytes.insubd (to_list _sk_seed) /\
      arg{2}.`3 = NBytes.insubd (to_list _pub_seed) /\
      arg{2}.`4 = a2 /\

      sub a1 0 5 = sub a2 0 5 
      
      ==>
      res{2} = EncodeWotsSignature res{1}.`1 /\
      sub res{1}.`2 0 5 = sub a1 0 5
    ].
proof.
rewrite /XMSS_N /XMSS_WOTS_LOG_W /XMSS_WOTS_W /XMSS_WOTS_LEN /XMSS_WOTS_LEN1 /XMSS_WOTS_LEN2.
move =>  [#] n_val logw_val w_val len1_val len2_val len_val *.
proc => /=.
conseq ( : 
  sub addr{1} 0 5 = sub a1 0 5 /\
  sub addr{1} 0 5 = sub address{2} 0 5 /\
  M{2} = to_list msg{1} /\
  val sk_seed{2} = to_list seed{1} /\ 
  val pub_seed{2} = to_list pub_seed{1}
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

(* ==================================================================================================== *)

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
          + auto => /> &1 &2 ??????H*.
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
            to_uint csum{1} = to_uint csum_32{2} /\
            0 <= to_uint csum_32{2} < W32.max_uint
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
            auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 result H15.
            move => k?.
            rewrite size_map size_to_list =>  Hk.
            rewrite (nth_map witness); first by rewrite size_to_list /#.
            rewrite get_to_list /#.
       
       auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13.
       rewrite size_map size_to_list => H14 *.
       split; last first.
          * move => k??. 
            rewrite initiE //=. 
            case (64 <= k < 67) => H; last first.
                    * have ->: to_uint lengths2{1}.[k] = nth witness (map W32.to_uint (sub lengths2{1} 0 64)) k.
                           + rewrite (nth_map witness) /=; first by rewrite size_sub /#.
                             rewrite nth_sub /#.
                      rewrite H6 (nth_map witness); first by rewrite size_to_list /#.
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
            rewrite H6 (nth_map witness); first by rewrite size_to_list /#.
            by rewrite get_to_list.
 
(* ==================================================================================================== *)

while (
    0 <= i{1} <= 67 /\
    ={i} /\
    size sig{2} = len /\
    val sk_seed{2} = to_list seed{1} /\
    val pub_seed{2} = to_list pub_seed{1} /\
    M{2} = to_list msg{1} /\ 

    sub addr{1} 0 5 = sub address{2} 0 5 /\
    sub addr{1} 0 5 = sub a1 0 5 /\

    map W32.to_uint (to_list lengths{1}) = msg{2} /\
    (forall (k : int), 0 <= k < 67 => 0 <= to_uint lengths{1}.[k] < w) /\
   
   
    sub sig{1} 0 (32 * i{1}) = sub_list (nbytes_flatten sig{2}) 0 (32 * i{1}) /\
    sub sig{1} (32 * i{1}) (67*32 - 32*i{1}) = sub (DecodeWotsSk wots_skey{2}) (32 * i{1}) (67*32 - 32*i{1}) 
); last first.
    + auto => /> &1 &2 H0 H1 H2 H3 H4 *.
      do split; 2: by smt().
        - apply (eq_from_nth witness); first by rewrite size_sub // size_sub_list.
          rewrite size_sub // /#.
        - move => addrL sigL addrR iR sigR H5 H6 H7 H8 H9 H10 H11 H12 H13.
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
          rewrite H12 /sub_list nth_mkseq 1:/# /= nth_nbytes_flatten /#.

wp; conseq />.

seq 2 1 : (#pre /\ sub address{2} 0 6 = sub addr{1} 0 6).
    + inline {1}; auto => /> &1 &2 *.
      rewrite /set_chain_addr.
      do split; (
          apply (eq_from_nth witness); [by rewrite !size_sub | rewrite size_sub // => j?];
          rewrite !nth_sub //= !get_setE //
      ).
         - rewrite ifF 1:/# ifF 1:/#; smt(sub_k).
         - smt(sub_k).
         - smt(sub_k).

inline {1} M(Syscall).__gen_chain_inplace_.
inline {1} M(Syscall)._gen_chain_inplace.

sp; wp.
exists * out0{1}, start0{1}, steps0{1}, pub_seed1{1}, addr1{1}, address{2}.        
elim * => _P1 _P2 _P3 _P4 _P5 _P6. 
call (gen_chain_correct _P1 _P2 _P3 _P4 _P5 _P6) => [/# |].

skip => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 *.
do split.
          + apply nbytes_eq.
            rewrite insubdK /=; first by rewrite /P size_to_list /#.
            apply (eq_from_nth witness); first by rewrite valP size_to_list /#.
            rewrite valP n_val => j?.
            rewrite get_to_list /= initiE //=.
            have ->: sig{1}.[i{2} * 32 + j] = nth witness (sub sig{1} (32 * i{2}) (2144 - 32 * i{2})) j by rewrite nth_sub /#.
            rewrite H9 /DecodeWotsSk nth_sub 1:/# get_of_list 1:/# nth_nbytes_flatten 2:/# valP /#.
          + rewrite (nth_map witness); [by rewrite size_to_list | by rewrite get_to_list].
          + rewrite -H4 #smt:(@NBytes).
          + smt().
          + smt().
          + smt().
          + smt().
          + smt().        
          + move => Ht H13 H14 H15 H16 H17 H18 resultL resultR H19 H20 H21.
            do split.
               * smt().
               * smt().
               * smt(size_put).
               * apply (eq_from_nth witness); first by rewrite !size_sub.
                 rewrite size_sub // => j?.
                 have ->: nth witness (sub resultR.`2 0 5) j = nth witness (sub resultR.`2 0 6) j by rewrite !nth_sub /#.
                 rewrite H21 -H12 !nth_sub // /#.
               * apply (eq_from_nth witness); first by rewrite !size_sub. 
                 rewrite size_sub 1:/# => j?.
                 rewrite nth_sub 1:/# nth_sub 1:/#; smt(sub_k).  
               * apply (eq_from_nth witness); first by rewrite size_sub 1:/# size_sub_list /#.
                 rewrite size_sub 1:/# => j?.
                 rewrite nth_sub 1:/# initiE 1:/# /=.
                 rewrite /sub_list nth_mkseq 1:/# /= nth_nbytes_flatten; first by smt(size_put). 
                 rewrite nth_put 1:/#.
                 case (i{2} = j %/ n) => //H.
                    * rewrite ifT 1:/# -get_to_list -H20 /#.
                    * rewrite ifF 1:/#.
                      have ->: sig{1}.[j] = nth witness (sub sig{1} 0 (32 * i{2})) j by rewrite nth_sub /#.
                      rewrite H8 /sub_list nth_mkseq 1:/# /= nth_nbytes_flatten /#.
               * apply (eq_from_nth witness); first by rewrite !size_sub /#.
                 rewrite size_sub 1:/# => j?.
                 rewrite nth_sub 1:/# initiE 1:/# /=.
                 rewrite nth_sub 1:/# /DecodeWotsSk.
                 case (i{2} * 32 <= 32 * (i{2} + 1) + j && 32 * (i{2} + 1) + j < i{2} * 32 + 32) => //= H.
                    * rewrite get_of_list 1:/# nth_nbytes_flatten /#.
                    * rewrite get_of_list 1:/# nth_nbytes_flatten; first by rewrite valP /#.
                      have ->: sig{1}.[32 * (i{2} + 1) + j] = nth witness (sub sig{1} (32 * i{2}) (2144 - 32 * i{2})) (32 + j) by rewrite nth_sub /#.
                      rewrite H9 nth_sub 1:/# /DecodeWotsSk get_of_list 1:/# nth_nbytes_flatten 2:/# valP /#.
               * smt().
               * smt().
qed.
