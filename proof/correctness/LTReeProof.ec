pragma Goals : printall.

require import AllCore List RealExp IntDiv Distr DList IntDiv.
from Jasmin require import JModel JArray.

require import Params Parameters Hash LTree.
require import XMSS_IMPL.

require import Repr2. 
require import Utils2.

require import Array4 Array8 Array32 Array64 Array68 Array96 Array132 Array136 Array352 Array2144.
require import WArray32 WArray96 WArray136.

require import Correctness_Address Correctness_Mem Correctness_Hash.
require import DistrUtils.

require import BitEncoding.
(*---*) import BitChunking.

require import StdBigop. 
(*---*) import Bigint.

require import Termination.

lemma ltree_correct (_pk : W8.t Array2144.t, _pub_seed : W8.t Array32.t, _addr : W32.t Array8.t) : 
    len = XMSS_WOTS_LEN /\ 
    n = XMSS_N /\ 
    padding_len = XMSS_PADDING_LEN /\
    prf_padding_val = XMSS_HASH_PADDING_PRF /\
    padding_len = XMSS_PADDING_LEN=>
    equiv [
      M(Syscall).__l_tree ~ LTree.ltree :
      _addr.[5] = W32.zero /\

      arg{1}.`2 = _pk /\
      arg{1}.`3 = _pub_seed /\
      arg{1}.`4 = _addr /\
      arg{2} = (EncodeWotsPk _pk, _addr, NBytes.insubd (to_list _pub_seed))
      ==>
      to_list res{1}.`1 = val res{2}.`1 /\ (* wots pk *)
      res{1}.`3 = res{2}.`2 (* address *)
    ].
proof. 
rewrite /XMSS_WOTS_LEN /XMSS_N.
move => [#] len_val n_val *.
proc. 
auto => />.
seq 4 0 : (
  addr{1} = address{2} /\
  pk{2} = EncodeWotsPk wots_pk{1} /\
  val _seed{2} = to_list pub_seed{1} /\
  to_uint l{1} = 67 /\
  address{2}.[5] = W32.zero
). 
    + auto => /> &2. 
      rewrite insubdK // /P size_to_list n_val //.
swap {2} 3 -1.
seq 2 3 : (
  #pre /\
  _len{2} = to_uint l{1} /\
  height{1} = W32.zero /\
  pks{2} = val pk{2}
).
    + inline {1}.
      auto => /> /#. 
(* At the end of the while loop, the first chunk is equal *)
seq 1 1 : (
  addr{1} = address{2} /\
  pks{2} = val pk{2} /\
  sub wots_pk{1} 0 32 = val (nth witness (val pk{2}) 0)
); last first.
    + ecall {1} (_x_memcpy_u8u8_post tmp{1}).
      auto => /> &1 &2 H0.
      apply (eq_from_nth witness); [by rewrite valP size_to_list n_val |]. 
      rewrite size_to_list => j?. 
      rewrite get_to_list initiE // #smt:(@List). 
(* ------------------------------------------------------------------------------- *)
(*                     At this point, we only have the while loop                  *)
(* ------------------------------------------------------------------------------- *)
while (
  addr{1} = address{2} /\
  val _seed{2} = to_list pub_seed{1} /\
   1 <= to_uint l{1} <= 67 /\
  _len{2} = to_uint l{1} /\
  pk{2} = EncodeWotsPk wots_pk{1} /\ 
  address{2}.[5] = height{1} /\
  pk{2} = EncodeWotsPk wots_pk{1} /\ 
  address{2}.[5] = height{1} /\
  pks{2} = val pk{2}
); last first.
    + auto => /> &1 &2 H0 H1 H2. 
      do split; 1..3:smt(). 
        * by rewrite /(\ult). 
        * move => lL pkL.
          rewrite /(\ult) (: to_uint W64.one = 1) // => ???? H3. 
          have E : to_uint lL = 1 by smt().           
          have := H3. 
          rewrite -enc_dec_wots_pk 1:/# -enc_comp_dec_pk // => H4.          
          apply (eq_from_nth witness); [by rewrite size_sub // valP n_val |].
          rewrite size_sub // => j?.
          rewrite /EncodeWotsPk nth_sub // insubdK. 
             - rewrite /P size_map size_chunk // size_to_list /#.
          rewrite /chunk (nth_map witness); [rewrite size_mkseq size_to_list /# |].
          rewrite nth_mkseq; [rewrite size_to_list /# |]. 
          rewrite insubdK => />.
             - rewrite /P size_take // size_drop // size_to_list n_val /#.
          rewrite nth_take 1,2:/# nth_drop // 1:/# get_to_list. 
          rewrite H4 //.           
(* ------------------------------------------------------------------------------- *)
(*              The first subgoal of the outter while loop starts here             *)
(* ------------------------------------------------------------------------------- *)
(* This removes the addresses at the end *)
seq 7 4 : (
  addr{1} = address{2} /\
  val _seed{2} = to_list pub_seed{1} /\
  1 <= to_uint l{1} <= 67 /\
  _len{2} = to_uint l{1} /\ 
  pks{2} = val pk{2} /\
  pk{2} = EncodeWotsPk wots_pk{1} /\ 
  address{2}.[5] = height{1} 
); last first.
    + inline {1}. 
      auto => /> &1 &2 *; do split. 
        * rewrite /get_tree_height /set_tree_height; congr ; smt(@W32). 
        * rewrite /get_tree_height /set_tree_height get_setE //=; smt(@W32).
        * rewrite /get_tree_height /set_tree_height get_setE //=; smt(@W32).
        * rewrite ultE (: to_uint W64.one = 1) //.        
        * rewrite ultE (: to_uint W64.one = 1) //.     
seq 2 0 : (#pre /\ to_uint parent_nodes{1} = to_uint l{1} %/ 2).
    + by auto => /> *; rewrite truncate_1_and_63 shr_1.

seq 2 2 : (
  addr{1} = address{2} /\
  val _seed{2} = to_list pub_seed{1} /\ 
  pks{2} = val pk{2} /\
  pk{2} = EncodeWotsPk wots_pk{1} /\
  _len{2} = to_uint l{1} /\
  address{2}.[5] = height{1} /\
  1 <= to_uint l{1} <= 67 /\ _len{2} = to_uint l{1} /\ 
  to_uint parent_nodes{1} = to_uint l{1} %/ 2
); last first.
(* The subgoal of seq starts here *)
seq 2 0 : (#pre /\ t{1} = l{1} `&` W64.one); first by auto.
if.
    + auto => /> &1 &2 *; smt(and_1_mod_2). 
    + seq 3 0 : (#pre /\ offset_out{1} = (l{1} `>>` W8.one) * W64.of_int 32); first by auto => /> &1 *; rewrite truncate_1_and_63.
      seq 3 0 : (#pre /\ offset_in{1}  = (l{1} - W64.one) * W64.of_int 32); first by auto => />.
      seq 1 2 : #pre.
        *  admit. (* HELP HERE *)
      auto => /> &1 &2 H0 H1 H2 H3 H4.
      do split. 
        * rewrite truncate_1_and_63 to_uintD_small; rewrite shr_1 (: to_uint W64.one = 1) // /#.
        * rewrite truncate_1_and_63 to_uintD_small; rewrite shr_1 (: to_uint W64.one = 1) // /#.
        * rewrite ifF 1:#smt:(and_1_mod_2) truncate_1_and_63 to_uintD_small; rewrite shr_1 (: to_uint W64.one = 1) // /#.
    + auto => /> &1 &2 H0 H1 H2 H3 H4. 
      do split. 
        * rewrite truncate_1_and_63 shr_1 #smt:(and_1_mod_2).
        * rewrite truncate_1_and_63 shr_1 #smt:(and_1_mod_2).
        * rewrite truncate_1_and_63 shr_1 ifT // #smt:(and_1_mod_2).
(* The subgoal of seq ends here *)
(* ------------------------------------------------------------------------------- *)
(*                         The inner while loop starts here                        *)
(* ------------------------------------------------------------------------------- *)
while (
  0 <= i{2} <= _len{2} %/ 2 /\
  i{2} = to_uint i{1} /\
  address{2} = addr{1} /\  
  pks{2} = val pk{2} /\
  pk{2} = EncodeWotsPk wots_pk{1} /\
  val _seed{2} = to_list pub_seed{1} /\
  address{2}.[5] = height{1} /\
  1 <= to_uint l{1} <= 67 /\ _len{2} = to_uint l{1} /\ 
  to_uint parent_nodes{1} = to_uint l{1} %/ 2
); last first. 
    + auto => /> &1 *. 
      do split => [/# | | ]; 1,2: by rewrite ultE (: to_uint W64.zero = 0) // /#.
seq 2 1 : (#pre); first by inline {1}; auto => />. 
seq 0 1 : (
  #pre /\
  pk_i{2} = nth witness pks{2} (2*i{2})
); first by auto.
seq 3 0 : (
  #pre /\ 
  to_list buf0{1} = sub wots_pk{1} (i{2} *32) 32
).
    + ecall {1} (memcpy_u8u8_2_32_2144_post wots_pk{1} offset_in{1}). 
      auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7.
      do split. 
         * rewrite to_uintM of_uintK //= /#. 
         * move => ?; rewrite to_uintM of_uintK //= /#. 
         * rewrite to_uintD to_uintM of_uintK //= /#.
         * rewrite to_uintD to_uintM of_uintK //= /#.
         * move => ????? ->. 
           congr.
           rewrite to_uintM of_uintK //= /#nqq. 
seq 4 0 : (
  #pre /\
  to_list buf1{1} = sub wots_pk{1} (i{2} * 64) 64
).
    + ecall {1} (memcpy_u8u8_2_64_2144_post wots_pk{1} offset_in{1}). 
      auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8.
      do split. 
         * rewrite to_uintM of_uintK //= /#. 
         * move => ?; rewrite !to_uintM !of_uintK //= /#. 
         * rewrite to_uintD to_uintM of_uintK //= /#.
         * rewrite to_uintD !to_uintM !of_uintK //= /#.
         * move => ????? ->. 
           congr.
           rewrite !to_uintM !of_uintK //= /#. 
seq 0 1 : (
  #pre /\
  buf1{1} = merge_nbytes_to_array pk_i{2} tmp{2}
).
    + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9.
      have E : forall (k : int), 0 <= k < 64 => buf1{1}.[k] = wots_pk{1}.[(to_uint i{1} * 64) + k] by smt(sub_ext). 
      rewrite tP => j?. 
      rewrite /merge_nbytes_to_array /EncodeWotsPk initiE // => />.  
      case (0 <= j < 32) => ?. 
         * rewrite insubdK; [rewrite /P size_map size_chunk // size_to_list len_val //= |].   
           rewrite (nth_map witness); [rewrite size_chunk // size_to_list //= /# |].
           rewrite insubdK.  
              - rewrite /P /chunk nth_mkseq; [rewrite size_to_list // /# |] => />.
                rewrite size_take // size_drop 1:/# size_to_list n_val /#.                
           rewrite /chunk nth_mkseq; [rewrite size_to_list /# |] => />.  
           rewrite nth_take // 1:/# nth_drop 1,2:/# get_to_list /#.
         * rewrite insubdK; [rewrite /P size_map size_chunk // size_to_list len_val //= |].   
           rewrite (nth_map witness); [rewrite size_chunk // size_to_list //= /# |].
           rewrite insubdK.  
              - rewrite /P /chunk nth_mkseq; [rewrite size_to_list // /# |] => />.
                rewrite size_take // size_drop 1:/# size_to_list n_val /#.                
           rewrite /chunk nth_mkseq; [rewrite size_to_list /# |] => />.  
           rewrite nth_take // 1:/# nth_drop 1,2:/# get_to_list /#. 

seq 1 1 : (
  0 <= i{2} <= _len{2} %/ 2 /\
  i{2} = to_uint i{1} /\
  address{2} = addr{1} /\
  pks{2} = val pk{2} /\
  pk{2} = EncodeWotsPk wots_pk{1} /\
  val _seed{2} = to_list pub_seed{1} /\
  1 <= to_uint l{1} <= 67 /\
  _len{2} = to_uint l{1} /\ 
  to_uint parent_nodes{1} = to_uint l{1} %/ 2 /\
  i{1} \ult parent_nodes{1} /\ 
  i{2} < _len{2} %/ 2 /\
  address{2}.[5] = height{1} /\
  to_list buf0{1} = val pk_i{2}
).
    + exists *  pk_i{2}, tmp{2}, pub_seed{1}, addr{1}.
      elim * => P0 P1 P2 P3. 
      call (rand_hash_correct P0 P1 P2 P3) => [/# |]. 
      auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9.
      do split. 
        * rewrite -H2 #smt:(@NBytes).
        * move => H10 rL rR H11 -> //.
          split => [// |]. 
          admit.
seq 2 1 : (#pre).
    + exists * wots_pk{1}, offset_out{1}, buf0{1}.
      elim * => P0 P1 P2.
      admit.
auto => /> &1 &2 *.
do split.  
    + smt().  
    + smt(). 
    + rewrite to_uintD (: to_uint W64.one = 1) // /#.
    + rewrite ultE to_uintD_small /#.
    + rewrite ultE to_uintD_small /#.
qed.

