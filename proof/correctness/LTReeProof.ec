pragma Goals : printall.

require import AllCore List RealExp IntDiv Distr DList IntDiv.
from Jasmin require import JModel JArray.

require import Types Params Parameters Address Hash WOTS LTree.
require import XMSS_IMPL.

require import Repr2. 
require import Utils2.

require import Array4 Array8 Array32 Array64 Array68 Array96 Array352 Array2144.
require import WArray32 WArray96.

require import Correctness_Address Correctness_Mem Correctness_Hash.
require import DistrUtils.

require import BitEncoding.
(*---*) import BitChunking.

require import StdBigop. 
(*---*) import Bigint.

require import Termination.

require import Array2144.

lemma memcpy_offset_ltree (wotspkImpl : W8.t Array2144.t)
                          (wotspkSpec : nbytes list)
                          (_idx_ : int) (_in_ : W8.t Array32.t) :
    len = XMSS_WOTS_LEN /\
    n = XMSS_N =>
    phoare [
      M(Syscall).__memcpy_u8u8_offset :
      arg.`1 = wotspkImpl /\
      arg.`2 = (of_int _idx_)%W64 * (of_int 32)%W64 /\  
      arg.`3 =  _in_ /\

      wotspkSpec = val (EncodeWotsPk wotspkImpl) /\
      0 <= _idx_ < len
      ==>
      res = DecodeWotsPk (
        LenNBytes.insubd (
        put wotspkSpec _idx_ (NBytes.insubd (to_list _in_))
        )
      )        
    ] = 1%r.
proof.
rewrite /XMSS_WOTS_LEN /XMSS_N => [#] len_val n_val.
proc => /=.
conseq (: 
  _ 
  ==> 
  sub out (32 * _idx_) 32 = to_list _in_ /\ 
  forall (k : int), 0 <= k < 2144 =>
     !(32 * _idx_ <= k < 32*_idx_ + 32) => 
      out.[k] = wotspkImpl.[k]
).
    + auto => /> H0 H1 out0.
      do split.
        - apply (eq_from_nth witness); first by rewrite size_to_list size_sub.
          rewrite size_sub // => j?.
          rewrite get_to_list nth_sub // /DecodeWotsPk get_of_list 1:/#.
          rewrite nth_nbytes_flatten; first by rewrite valP /#.
          rewrite insubdK; first by rewrite /P size_put valP.
          rewrite nth_put; first by rewrite /P valP /#.
          rewrite ifT 1:/#.
          rewrite insubdK; first by rewrite /P size_to_list /#.
          by rewrite get_to_list /#.
        - move => k?? Hk.
          rewrite /DecodeWotsPk get_of_list 1:/#.
          rewrite nth_nbytes_flatten; first by rewrite valP /#.
          rewrite insubdK; first by rewrite /P size_put valP.
          rewrite nth_put; first by rewrite /P valP /#.
          rewrite ifF 1:/#.       
          rewrite /EncodeWotsPk insubdK; first by rewrite /P size_map size_chunk 1:/# size_to_list /#.
          rewrite (nth_map witness); first by rewrite size_chunk 1:/# size_to_list /#.       
          rewrite insubdK. 
            * rewrite /P /chunk nth_mkseq /=; first by rewrite size_to_list /#.
              rewrite size_take 1:/#.
              rewrite size_drop 1:/# size_to_list /#.
          rewrite /chunk nth_mkseq /=. 
            * rewrite size_to_list /#.  
          rewrite nth_take 1..2:/# nth_drop 1..2:/# get_to_list /#.
        - move => H2 H3.
          rewrite tP => j?.
          rewrite /DecodeWotsPk get_of_list //.
          rewrite nth_nbytes_flatten.
            * rewrite valP /#. 
          rewrite insubdK; first by rewrite /P size_put valP.
          rewrite nth_put; first by rewrite /P valP /#.
          case (_idx_ = j %/ n) => ?.
              + rewrite -H2 insubdK; first by rewrite /P size_sub // /#.
                by rewrite nth_sub /#.
              + rewrite H3 // 1:/#.             
                rewrite /EncodeWotsPk insubdK; first by rewrite /P size_map size_chunk 1:/# size_to_list /#.
                rewrite (nth_map witness); first by rewrite size_chunk 1:/# size_to_list /#.       
                rewrite insubdK. 
                * rewrite /P /chunk nth_mkseq /=; first by rewrite size_to_list /#.
                  rewrite size_take 1:/#.
                  rewrite size_drop 1:/# size_to_list /#.
                rewrite /chunk nth_mkseq /=. 
                * rewrite size_to_list /#.  
                  rewrite nth_take 1..2:/# nth_drop 1..2:/# get_to_list /#.

(* ------------------------------------------------------------------------------- *)
(*    end of proof for conseq                                                      *)
(* ------------------------------------------------------------------------------- *)
while 
( 
  in_0 = _in_ /\
  0 <= _idx_  < len /\
  offset = (of_int (_idx_ * 32))%W64 + i /\

  0 <= to_uint i <= 32 /\
  sub out (32 * _idx_) (to_uint i) = sub _in_ 0 (to_uint i) /\

  forall (k : int),
    0 <= k && k < 2144 =>
    ! (32 * _idx_ <= k < 32 * _idx_ + to_uint i) => out.[k] = wotspkImpl.[k]
  
)
(32 - to_uint i); last first.
  + auto => /> H0 H1.
    split.
     - apply (eq_from_nth witness); rewrite !size_sub /#.
     - move => i0 out0.
       split; first by move => *; rewrite ultE /#.
       rewrite ultE of_uintK /= => H2 H3 H4.
       have E: to_uint i0 = 32 by smt().
       rewrite E => H5 H6.
       split.
         * rewrite H5.
           apply (eq_from_nth witness); first by rewrite size_to_list size_sub. 
           rewrite size_sub // => j?.
           by rewrite get_to_list nth_sub.
         * move => k?? Hk.
           by apply H6.
 
  + auto => /> &hr H0 H1 H2 H3 H4 H5.
    rewrite ultE of_uintK /= => H6.
    do split.
     - by ring.
     - rewrite to_uintD /#.
     - rewrite to_uintD /#.
     - apply (eq_from_nth witness); first by rewrite !size_sub // to_uintD /#.
       rewrite size_sub; first by rewrite to_uintD /#.
       rewrite to_uintD_small 1:/# /= => j?.
       rewrite !nth_sub //= get_setE; first by smt(@W64).
       case (to_uint i{hr} = j) => ?.
         * rewrite ifT 2:/#; smt(@W64 pow2_64). 
         * rewrite ifF; first by smt(@W64 pow2_64).
           have ->: _in_.[j] = nth witness (sub _in_ 0 (to_uint i{hr})) j by rewrite nth_sub // /#.
           by rewrite -H4 nth_sub /#.
     - move => k?? Hk.
       rewrite !get_setE; first by smt(@W64 pow2_64).
       rewrite H5 //; first by smt(@W64 pow2_64).
       by rewrite ifF; smt(@W64 pow2_64).
     - rewrite to_uintD /#.
qed.


(*  proc ltree(pk : wots_pk, address : adrs, _seed : seed) : nbytes *)
lemma ltree_correct (_pk : W8.t Array2144.t, _pub_seed : W8.t Array32.t, a0 a1 : W32.t Array8.t) : 
    len = XMSS_WOTS_LEN /\ 
    n = XMSS_N /\ 
    padding_len = XMSS_PADDING_LEN /\
    prf_padding_val = XMSS_HASH_PADDING_PRF /\
    padding_len = XMSS_PADDING_LEN =>
    equiv [
      M(Syscall).__l_tree_ ~ LTree.ltree :
      arg{1}.`2 = _pk /\
      arg{1}.`3 = _pub_seed /\
      arg{1}.`4 = a0 /\

      arg{2}.`1 = EncodeWotsPk _pk /\
      arg{2}.`2 = a0 /\
      arg{2}.`3 = NBytes.insubd (to_list _pub_seed) /\
      

      sub a0 0 5 = sub a1 0 5
      ==>
      to_list res{1}.`1 = val res{2} /\
      sub res{1}.`3 0 5 = sub a0 0 5
    ].
proof. 
rewrite /XMSS_WOTS_LEN /XMSS_N.
move => [#] len_val n_val *.
proc => /=. 
seq 4 0 : #pre; first by auto.
seq 1 5 : #post; last by auto.

swap 2 -1.

seq 0 1 : (
  pks{2} = val (EncodeWotsPk wots_pk{1}) /\
  _seed{2} = (insubd (to_list pub_seed{1}))%NBytes /\
  sub addr{1} 0 5 = sub address{2} 0 5 /\
  sub addr{1} 0 5 = sub a0 0 5
); first by auto.


inline  M(Syscall)._l_tree M(Syscall).__l_tree.
 
seq 11 0 : (
  pks{2} = val (EncodeWotsPk wots_pk1{1}) /\
  _seed{2} = (insubd (to_list pub_seed1{1}))%NBytes /\
  sub addr1{1} 0 5 = sub address{2} 0 5 /\
  sub addr1{1} 0 5 = sub a0 0 5
); first by auto.

seq 3 2: (
  #{/~sub addr1{1} 0 5 = sub address{2} 0 5}pre /\
  sub addr1{1} 0 6 = sub address{2} 0 6 /\
  to_uint l{1} = _len{2} /\
  _len{2} = 67 /\  
  height{1} = address{2}.[5] /\
  height{1} = W32.zero
).
    + inline {1}.
      auto => /> &1 &2 H0 H1.
      do split; last by rewrite len_val.
        - apply (eq_from_nth witness); rewrite !size_sub // => j?.
          case (j = 5) =>  ?.
            * rewrite /set_tree_height !nth_sub // !get_setE // /#.
            * rewrite !nth_sub // !get_setE //= ifF 1:/#; smt(sub_k).
        - apply (eq_from_nth witness); rewrite !size_sub // => j?.
          case (j = 5) =>  ?.
            * rewrite /set_tree_height !nth_sub // !get_setE // /#.
            * rewrite !nth_sub // !get_setE //= ifF 1:/#; smt(sub_k).
 
seq 1 1 : (
 sub wots_pk1{1} 0 n = val (nth witness pks{2} 0) /\
 sub addr1{1} 0 5 = sub a0 0 5
); last first.
    + wp; sp.
      ecall {1} (_x_memcpy_u8u8_post tmp{1}); conseq />.
      skip => /> &1 &2 <- H1.
      apply (eq_from_nth witness); first by rewrite size_to_list size_sub n_val.
      rewrite size_to_list => j?.
      by rewrite get_to_list n_val nth_sub // initiE.
  
while (
  pks{2} = val (EncodeWotsPk wots_pk1{1}) /\
  val _seed{2} = to_list pub_seed1{1} /\
  to_uint l{1} = _len{2} /\
  1 <= _len{2} <= 67 /\
  sub addr1{1} 0 5 = sub a0 0 5 /\ 
  sub addr1{1} 0 6 = sub address{2} 0 6 /\
  to_uint height{1} = get_tree_height address{2} /\
  height{1} = address{2}.[5] 
); last first.
    + auto => /> &1 &2 H0 H1 H2 *.
      do split.
        - by rewrite insubdK // /P size_to_list n_val.
        - by rewrite H2.
        - by rewrite H2.
        - by rewrite ultE.
        - by rewrite ultE. 
        - move => addrL lL pkL addrR.
          rewrite ultE => H4 H5 H6 H7 H8 H9 H10 H11.
          apply (eq_from_nth witness); first by rewrite valP n_val size_sub.
          rewrite size_sub n_val // => j?.
          rewrite /EncodeWotsPk insubdK.
            * rewrite /P size_map size_chunk 1:/# size_to_list /#.
          rewrite nth_sub //= (nth_map witness).
            * rewrite size_chunk 1:/# size_to_list /#.
          rewrite insubdK.
            * rewrite /P /chunk nth_mkseq /=; first by rewrite size_to_list /#.
              rewrite size_take 1:/# /= size_drop // size_to_list /#.
          rewrite /chunk nth_mkseq /=; first by rewrite size_to_list /#.
          rewrite nth_take 1..2:/# nth_drop 1..2:/# get_to_list.
          trivial.

seq 2 0 : (#pre /\ to_uint parent_nodes{1} = _len{2} %/ 2).
    + by auto => /> *; rewrite truncate_1_and_63 to_uint_shr.

seq 5 4 : #post; last first.
    + conseq />.
      inline {1}; auto => /> &1 &2 H0 H1 H2 H3 H4 H5.
      rewrite ultE => H6.
      do split.
        - apply (eq_from_nth witness); first by rewrite !size_sub.
          rewrite size_sub // => j?.
          rewrite !nth_sub //= get_setE // ifF 1:/#; smt(sub_k).
        - apply (eq_from_nth witness); first by rewrite !size_sub.
          rewrite size_sub // => j?.
          rewrite !nth_sub //= get_setE // /get_tree_height /set_tree_height. 
          case (j = 5) => ?.
             * rewrite get_setE // ifT //; smt(@W32 pow2_32).
             * rewrite get_setE // ifF 1:/#; smt(sub_k).
        - rewrite /get_tree_height /set_tree_height.
          rewrite get_setE //=; smt(@W32 pow2_32).
        - rewrite /get_tree_height /set_tree_height.
          rewrite get_setE //=; smt(@W32 pow2_32).
 
seq 2 2 : #post.
 
(* ------------------------------------------------------------------------------- *)
(*                                                                                 *)
(* ------------------------------------------------------------------------------- *)

while (
    #pre /\ 
    0 <= to_uint i{1} <= to_uint parent_nodes{1} /\
    i{2} = to_uint i{1}
); last by auto => /> &1 &2 *; rewrite ultE /#.

seq 2 1 : (#pre /\ sub addr1{1} 0 7 = sub address{2} 0 7).
    + inline {1}; auto => /> *.
      rewrite /set_tree_index.
      do split; (apply (eq_from_nth witness); rewrite !size_sub // => j?).
        - rewrite !nth_sub //= !get_setE // ifF 1:/#; smt(sub_k).
        - rewrite !nth_sub //= !get_setE // ifF 1:/# ifF 1:/#; smt(sub_k).
        - rewrite !nth_sub //= !get_setE //.
          case (j = 6) => ?; [smt(@W32 pow2_32) | smt(sub_k)]. 

seq 4 2 : (
  #pre /\
  to_list buf1{1} = val pk_i{2} ++ val tmp{2}
).
    + sp.
      ecall {1} (memcpy_u8u8_2_64_2144_post wots_pk1{1} offset_in{1}).
      skip => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13.
      do split; 1..3: by smt(@W64 pow2_64).
        - smt(@W64 pow2_64 @IntDiv).
        - move => ???? result H.
          rewrite H.
          apply (eq_from_nth witness); first by rewrite size_cat !valP n_val size_sub.
          rewrite size_sub // => j?.
          rewrite /EncodeWotsPk insubdK.
             * rewrite /P size_map size_chunk 1:/# size_to_list /#.
          rewrite nth_sub //=.
          rewrite (nth_map witness); first by rewrite size_chunk 1:/# size_to_list /#.
          rewrite insubdK.
             * rewrite /P /chunk nth_mkseq /=; first by rewrite size_to_list /#.
               rewrite size_take 1:/# size_drop 1:/# size_to_list /#.
          rewrite /chunk nth_mkseq /=; first by rewrite size_to_list /#.
          case (0 <= j < 32) => [Hfst | Hsnd].
             * rewrite nth_cat size_take 1:/# size_drop 1:/# size_to_list ifT 1:/#.
               rewrite nth_take 1,2:/#.
               rewrite nth_drop 1,2:/#.
               by rewrite get_to_list; congr; smt(@W64 pow2_64).
             * rewrite nth_cat size_take 1:/# size_drop 1:/# size_to_list ifF 1:/#.
               rewrite (nth_map witness); first by rewrite size_mkseq /#.
               rewrite insubdK; first by rewrite /P nth_mkseq 1:/# /= size_take 1:/# size_drop 1:/# size_to_list /#.
               rewrite nth_mkseq 1:/# /= ifT 1:/#.
               rewrite nth_take 1,2:/# nth_drop 1,2:/#.
               by rewrite get_to_list; congr; smt(@W64 pow2_64).

seq 1 1 : (
    #{/~to_list buf1{1} = val pk_i{2} ++ val tmp{2}}pre /\
    to_list buf0{1} = val pk_i{2}
).
    + exists * pk_i{2}, tmp{2}, pub_seed1{1}, addr1{1}, address{2}.
      elim * => P0 P1 P2 P3 P4.
      call (rand_hash_results P0 P1 P2 P3 P4) => [/# |].
      skip => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14*.
      do split.
        - rewrite tP => j?.
          rewrite -get_to_list H14.
          case (0 <= j < 32) => [Hfst | Hsnd].
            * rewrite nth_cat valP ifT 1:/# /merge_nbytes_to_array.
              by rewrite initiE //= ifT.
            * rewrite nth_cat valP ifF 1:/# /merge_nbytes_to_array.
              rewrite initiE //= ifF /#.
        - rewrite -H0; smt(@NBytes).
        - smt(sub_k).
        - move => ??? resL resR Ha Hb.
          do split; (apply (eq_from_nth witness); rewrite !size_sub // => j?).
            * rewrite !nth_sub //; smt(sub_k).
            * rewrite !nth_sub //; smt(sub_k).
            * rewrite !nth_sub //; smt(sub_k).

wp.
exists * wots_pk1{1}, pks{2}, (to_uint i{1}), buf0{1}.
elim * => P0 P1 P2 P3.
call {1} (memcpy_offset_ltree P0 P1 P2 P3) => [/# |].
auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14.
do split.
- smt(@W64 pow2_64).
- smt().
- move => H15 H16.
  do split; 2..6: by smt(@W64 pow2_64).
  apply (eq_from_nth witness); first by rewrite size_put !valP.
  rewrite size_put valP len_val => j?.
  rewrite nth_put; first by rewrite valP /#.
  rewrite /EncodeWotsPk insubdK.
    + rewrite /P size_map size_chunk 1:/# size_to_list /#.
  rewrite insubdK.
    + rewrite /P size_map size_chunk 1:/# size_to_list /#.
  rewrite /DecodeWotsPk.
  rewrite insubdK.
    + rewrite /P size_put size_map size_chunk 1:/# size_to_list /#.
  rewrite (nth_map witness); first by rewrite size_chunk 1:/# size_to_list /#.
  rewrite (nth_map witness) /=; first by rewrite size_iota size_to_list /#.
  rewrite size_to_list nth_iota 1:/#.
  rewrite (nth_map witness); first by rewrite size_chunk 1:/# size_to_list /#.
  rewrite /chunk nth_mkseq /=; first by rewrite size_to_list /#.
  case (to_uint i{1} = j) => [<- | ?].
    + apply nbytes_eq.
      apply (eq_from_nth witness); first by rewrite !valP.
      rewrite valP n_val => k?.
      rewrite H14 insubdK.
        * rewrite /P size_take // size_drop 1:/# size_to_list /#.
      rewrite size_to_list nth_take // 1:/#.   
      rewrite nth_drop 1,2:/# get_to_list get_of_list 1:/#.
      rewrite nth_nbytes_flatten; first by rewrite size_put size_map size_mkseq /#.
      rewrite nth_put; first by rewrite size_map size_mkseq /#.
      rewrite ifT 1:/#.
      by rewrite insubdK 2:/# /P valP.
    + apply nbytes_eq.
      apply (eq_from_nth witness); first by rewrite !valP.
      rewrite valP n_val => k?.
      rewrite H14 insubdK.
        * rewrite /P size_take // size_drop 1:/# size_to_list /#.
      rewrite size_to_list nth_take // 1:/#.   
      rewrite nth_drop 1,2:/# get_to_list insubdK.
        * rewrite /P size_take // size_drop // 1:/# size_to_list /#.
      rewrite nth_take // 1:/#.   
      rewrite nth_drop 1,2:/# get_to_list get_of_list 1:/#.
      rewrite nth_nbytes_flatten; first by rewrite size_put size_map size_mkseq /#.
      rewrite nth_put; first by rewrite size_map size_mkseq /#.
      rewrite ifF 1:/#.
      rewrite (nth_map witness); first by rewrite /P size_mkseq /#.
      rewrite insubdK; first by  rewrite /P nth_mkseq 1:/# /= size_take // size_drop // 1:/# size_to_list /#.
      rewrite nth_mkseq 1:/# /= nth_take // 1:/# nth_drop 1,2:/# get_to_list /#.

(* ------------------------------------------------------------------------------- *)
(*                                                                                 *)
(* ------------------------------------------------------------------------------- *)

seq 2 0 : (
  pks{2} = val (EncodeWotsPk wots_pk1{1}) /\
  val _seed{2} = to_list pub_seed1{1} /\
  to_uint l{1} = _len{2} /\
  1 <= _len{2} <= 67 /\
  sub addr1{1} 0 5 = sub a0 0 5 /\
  sub addr1{1} 0 6 = sub address{2} 0 6 /\
  to_uint height{1} = get_tree_height address{2} /\
  height{1} = address{2}.[5] /\
  (W64.one \ult l{1} <=> 1 < _len{2}) /\
  (t{1} <> W64.zero <=> _len{2} %% 2 = 1)
); first by auto => />  &1 &2 * ; smt(and_1_mod_2).

case (t{1} <> W64.zero); last first.
    + rcondf {1} 1; first by auto.
      rcondf {2} 1; first by auto => /> /#.
      auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7.
      do split.
        - rewrite ifT 1:/# (: 63 = 2^6 - 1) 1:/# and_mod //.
          rewrite to_uint_shr 1:/# /=.
          have ->: to_uint (truncateu8 W256.one) %% 64 = 1 by rewrite to_uint_truncateu8.
          by [].
        - rewrite ifT /#.
        - rewrite ifT /#.
        - rewrite ifT 1:/# (: 63 = 2^6 - 1) 1:/# and_mod //.
          rewrite ultE /=.
          have ->: to_uint (truncateu8 W256.one) %% 64 = 1 by rewrite to_uint_truncateu8.
          by rewrite to_uint_shr.
        - rewrite ifT 1:/# (: 63 = 2^6 - 1) 1:/# and_mod //.
          rewrite ultE /=.
          have ->: to_uint (truncateu8 W256.one) %% 64 = 1 by rewrite to_uint_truncateu8.
          by rewrite to_uint_shr.


    + rcondt {1} 1; first by auto.
      rcondt {2} 1; first by auto => /> /#.
      conseq />.

      seq 2 0 : (#pre /\ to_uint offset_out{1} = _len{2} %/ 2).
        - auto => /> &1 &2 *.
          rewrite (: 63 = 2^6 - 1) 1:/# and_mod //.
          have ->: to_uint (truncateu8 W256.one) %% 64 = 1 by rewrite to_uint_truncateu8.
          by rewrite to_uint_shr.

      seq 1 0 : (
           #{/~to_uint offset_out{1} = _len{2} %/ 2}pre /\ 
           to_uint offset_out{1} = (_len{2} %/ 2) * 32
      ); first by auto => /> ???????????H; rewrite to_uintM H of_uintK /#.

      seq 3 0 : (
        #pre /\ 
        to_uint offset_in{1} = (_len{2} - 1) * 32
      ); first by auto => /> *; rewrite to_uintM of_uintK /= to_uintB 2:/# uleE /#.

      seq 1 2 : #pre; last first.
        - auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 *.
          do split.
            * rewrite ifF 1:/# (: 63 = 2^6 - 1) 1:/# and_mod //.
              have ->: to_uint (truncateu8 W256.one) %% 64 = 1 by rewrite to_uint_truncateu8.
              rewrite to_uintD to_uint_shr 1:/# /= to_uint_truncateu8.
              smt().
            * smt().
            * smt().
            * rewrite ifF 1:/# ultE (: 63 = 2^6 - 1) 1:/# and_mod //.
              rewrite to_uintD of_uintK /=. 
              rewrite to_uint_shr 1:/# /=.
              have ->: to_uint (truncateu8 W256.one) %% 64 = 1 by rewrite to_uint_truncateu8.
              smt().
            * rewrite ifF 1:/# ultE (: 63 = 2^6 - 1) 1:/# and_mod //.
              rewrite to_uintD of_uintK /=. 
              rewrite to_uint_shr 1:/# /=.
              have ->: to_uint (truncateu8 W256.one) %% 64 = 1 by rewrite to_uint_truncateu8.
              smt().

   
inline {1}.
sp 3 0.
conseq />.

seq 2 2 : (pks{2} = val (EncodeWotsPk out{1})); last by auto.
wp.
 
while {1} 
(
  pks{2} = val (EncodeWotsPk wots_pk1{1}) /\
  0 <= i0{1} <= 32 /\ 
  to_uint offset_out0{1} = (_len{2} %/ 2 * 32) /\
  to_uint offset_in0{1} = (_len{2} - 1) * 32 /\
  to_uint offset_out{1} = (_len{2} %/ 2 * 32) /\
  to_uint offset_in{1} = (_len{2} - 1) * 32 /\

  1 <= _len{2} <= 67 /\

  sub out{1} (to_uint offset_out{1}) i0{1} = 
  sub_list (val (nth witness pks{2} (_len{2} - 1))) 0 i0{1} /\
  
  forall (k : int), 0 <= k < 2144 => 
    !(to_uint offset_out{1} <= k < to_uint offset_out{1} + i0{1}) =>
       out{1}.[k] = nth witness (nbytes_flatten pks{2}) k
)
(32 - i0{1}); last first.
  + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.
    do split.
      - apply (eq_from_nth witness); first by rewrite size_sub // size_sub_list.
        rewrite size_sub /#.
      - move => k???.
        rewrite nth_nbytes_flatten; first by rewrite valP /#.
        rewrite /EncodeWotsPk insubdK.
          * rewrite /P size_map size_chunk 1:/# size_to_list /#.
        rewrite (nth_map witness).
          * rewrite size_chunk 1:/# size_to_list /#.
        rewrite insubdK.
          * rewrite /P /chunk nth_mkseq /=; first by rewrite size_to_list /#.
            rewrite size_take 1:/# size_drop 1:/# size_to_list /#.
        rewrite /chunk nth_mkseq /=; first by rewrite size_to_list /#.
        rewrite nth_take 1,2:/# nth_drop 1,2:/# get_to_list /#.
      - move => i0L outL. 
        split => [/# |].
        move => H11 H12 H13.
        have E: i0L = 32 by smt().
        rewrite E => H14 H15.
        apply (eq_from_nth witness); first by rewrite size_put !valP.
        rewrite size_put valP len_val => j?.
        rewrite nth_put; first by rewrite valP /#.
        rewrite /EncodeWotsPk !insubdK.
          * rewrite /P size_map size_chunk 1:/# size_to_list /#.
          * rewrite /P size_map size_chunk 1:/# size_to_list /#.
        case (j = to_uint l{1} %/ 2) => [Ha | Hb].
          * rewrite ifT Ha // (nth_map witness).
              + rewrite size_chunk 1:/# size_to_list /#.
            rewrite /chunk nth_mkseq /=; first by rewrite size_to_list /#.
            apply nbytes_eq.
            rewrite insubdK; first by rewrite /P size_take 1:/# size_drop 1:/# size_to_list /#.
            rewrite (nth_map witness); first by rewrite size_mkseq size_to_list /#.
            rewrite insubdK.
              + rewrite /P size_to_list nth_mkseq /= 1:/# size_take 1:/# size_drop 1:/# size_to_list /#.
            rewrite nth_mkseq /=;first by rewrite size_to_list /#.
            apply (eq_from_nth witness); first by rewrite !size_take 1,2:/# !size_drop 1,2:/# !size_to_list /#.
            rewrite size_take 1:/# size_drop 1:/# size_to_list.
            rewrite (: max 0 (2144 - n * (to_uint l{1} - 1)) = 2144 - n * (to_uint l{1} - 1)) 1:/#.
            rewrite n_val /= => k?.
            rewrite !nth_take 1..4:/# !nth_drop 1..4:/# !get_to_list.
            have ->: outL.[32 * (to_uint l{1} %/ 2) + k] = nth witness (sub outL (to_uint offset_out{1}) 32) k.
              + rewrite nth_sub /#.              
            rewrite H14 /sub_list nth_mkseq /= 1:/# /EncodeWotsPk.
            rewrite insubdK.
              + rewrite /P size_map size_chunk 1:/# size_to_list /#.
            rewrite (nth_map witness); first by rewrite size_chunk 1:/# size_to_list /#.
            rewrite insubdK.
              + rewrite /P /chunk nth_mkseq /=; first by rewrite size_to_list /#.
                rewrite size_take 1:/# /= size_drop 1:/# size_to_list /#.
            rewrite /chunk nth_mkseq /=; first by rewrite size_to_list /#.
            rewrite nth_take 1..2:/# nth_drop 1..2:/# get_to_list.
            by rewrite n_val.

          * rewrite ifF 1:/#.
            rewrite (nth_map witness).
              + rewrite size_chunk 1:/# size_to_list /#.
            rewrite /chunk nth_mkseq /=; first by rewrite size_to_list /#.
            apply nbytes_eq.
            rewrite insubdK.
              + rewrite /P size_take 1:/# size_drop 1:/# size_to_list /#.
            rewrite (nth_map witness); first by rewrite size_mkseq size_to_list /#.
            rewrite insubdK.
              + rewrite /P nth_mkseq /=; first by rewrite size_to_list /#.
                rewrite size_take 1:/# size_drop 1:/# size_to_list /#.
            rewrite nth_mkseq /=; first by rewrite size_to_list /#.
            apply (eq_from_nth witness).
              + rewrite !size_take 1,2:/# !size_drop 1,2:/# !size_to_list /#. 
            rewrite size_take 1:/# size_drop 1:/# size_to_list.
            rewrite (: max 0 (2144 - n * j) =  (2144 - n * j)) 1:/#.
            move => i?.
            rewrite !nth_take 1..4:/# !nth_drop 1..4:/#.
            rewrite !get_to_list.
            rewrite H15 1,2:/#.
            rewrite nth_nbytes_flatten.
              + rewrite valP /#.
            rewrite /EncodeWotsPk insubdK.
              + rewrite /P size_map size_chunk 1:/# size_to_list /#.
            rewrite (nth_map witness); first by rewrite size_chunk 1:/# size_to_list /#.
            rewrite insubdK.
              + rewrite /P /chunk nth_mkseq /=; first by rewrite size_to_list /#.
                rewrite size_take 1:/# /= size_drop 1:/# size_to_list /#.
            rewrite /chunk nth_mkseq /=; first by rewrite size_to_list /#.
            by rewrite nth_take 1..2:/# nth_drop 1..2:/# get_to_list /#.


(* first subgoal of while here *)
  + auto => /> &hr H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10*.
    do split; 1,2,5: by smt().
      - apply (eq_from_nth witness); first by rewrite size_sub 1:/# size_sub_list /#.
        rewrite size_sub 1:/# => j?.
        rewrite nth_sub // get_setE. 
          * rewrite !to_uintD of_uintK /= /#. 
        case (j = i0{hr}) => [Ha | Hb].
          * rewrite ifT; first by smt(@W64 pow2_64).
            rewrite /sub_list nth_mkseq /= 1:/#.
            have ->: to_uint (offset_in0{hr} + (of_int i0{hr})%W64) = 
                     to_uint offset_in0{hr} + i0{hr} by smt(@W64 pow2_64).
            rewrite H9 1,2:/#.
            rewrite nth_nbytes_flatten; first by rewrite valP /#.
            rewrite /EncodeWotsPk /#.
          * rewrite ifF; first by smt(@W64 pow2_64).
            have ->: out{hr}.[to_uint offset_out{hr} + j] = 
                     nth witness (sub out{hr} (to_uint offset_out{hr}) i0{hr}) j
                     by rewrite nth_sub /#.
            rewrite H8 /sub_list !nth_mkseq /#. 
      - move => k?? Hk.
        rewrite get_setE; first by smt(@W64 pow2_64).
        rewrite ifF; first by smt(@W64 pow2_64).
        by rewrite H9 1,2:/#.
qed.



