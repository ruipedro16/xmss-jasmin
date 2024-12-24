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

(* INLEN = 32 /\ OUTLEN = 2144 *)
(* pre: copying all elements of in does not write out of bounds in out *)
(* 0 <= offset + 32 <= 2144 *)
(* 0 <= offset <= 2112 *)
(* same as memcpy(out + offset, in, sizeof(in)); *)

lemma memcpy_offset_ltree (wotspkImpl : W8.t Array2144.t)
                          (wotspkSpec : wots_pk)
                          (_idx_ : int) (_in_ : W8.t Array32.t) :
    len = XMSS_WOTS_LEN /\
    n = XMSS_N =>
    phoare [
      M(Syscall).__memcpy_u8u8_offset :
      arg.`1 = wotspkImpl /\
      arg.`2 = (of_int _idx_)%W64 * (of_int 32)%W64 /\  
      arg.`3 =  _in_ /\

      wotspkSpec = EncodeWotsPk wotspkImpl /\
      0 <= _idx_ < len
      ==>
      res = DecodeWotsPk (
        LenNBytes.insubd (
        put (val wotspkSpec) _idx_ (NBytes.insubd (to_list _in_))
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
inline  M(Syscall)._l_tree M(Syscall).__l_tree.

seq 11 0 : (
  pk{2} = EncodeWotsPk wots_pk1{1} /\
  _seed{2} = (insubd (to_list pub_seed1{1}))%NBytes /\
  sub addr1{1} 0 5 = sub address{2} 0 5 /\
  sub addr1{1} 0 5 = sub a0 0 5
); first by auto.

swap {2} 3 -2.

seq 3 2: (
  #{/~sub addr1{1} 0 5 = sub address{2} 0 5}pre /\
  sub addr1{1} 0 6 = sub address{2} 0 6 /\
  to_uint l{1} = _len{2} /\
  _len{2} = 67
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

sp; wp.

seq 1 1 : (
  sub addr1{1} 0 5  = sub a0 0 5 /\ 
  sub wots_pk1{1} 0 32 = val (nth witness pks{2} 0)
); last first. 
    + ecall {1} (_x_memcpy_u8u8_post tmp{1}); conseq />.
      auto => /> &1 &2 H0 <-.
      apply (eq_from_nth witness); first by rewrite size_to_list size_sub.      
      rewrite size_to_list => j?.
      by rewrite nth_sub // get_to_list initiE.

 
while (
  pk{2} = EncodeWotsPk wots_pk1{1} /\
  val _seed{2} = to_list pub_seed1{1} /\
  pks{2} = val pk{2} /\
  to_uint l{1} = _len{2} /\
  1 <= _len{2} <= 67 /\
  sub addr1{1} 0 5 = sub a0 0 5 /\ 
  sub addr1{1} 0 6 = sub address{2} 0 6
); last first.
    + auto => /> &1 &2 H0 H1 H2.
      do split.
        - by rewrite insubdK // /P size_to_list n_val.
        - by rewrite H2.
        - by rewrite H2.
        - by rewrite ultE.
        - by rewrite ultE.
        - move => addrL lL pkL addrR.
          rewrite ultE => H3 H4 -> H6 H7 H8 H9 H10. 
          apply (eq_from_nth witness); first by rewrite valP n_val size_sub.
          rewrite size_sub // => j?.
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

seq 5 5 : (to_uint height{1} = tree_height{2} /\ #post); last first.
    + inline {1}; auto => /> &1 &2 H0 H1 H2 H3 H4 H5.
      split.
         * apply (eq_from_nth witness); rewrite !size_sub // => j?.
           rewrite !nth_sub //= get_setE // ifF 1:/#.
           smt(sub_k).
         * apply (eq_from_nth witness); rewrite !size_sub // => j?.
           rewrite !nth_sub /set_tree_height //= !get_setE //.
           case (j = 5) => ?; smt(@W32 pow2_32 sub_k).

seq 2 2 : #pre.

(* ------------------------------------------------------------------------------- *)
(*                                                                                 *)
(* ------------------------------------------------------------------------------- *)

while (
  #pre /\ 
  to_uint i{1} = i{2} /\ 
  0 <= i{2} <= _len{2} %/ 2
); last first.
    + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7.
      split => [/# |].
      rewrite ultE /= /#.

seq 2 1 : (
  #{/~sub addr1{1} 0 6 = sub address{2} 0 6}pre /\
  sub addr1{1} 0 7 = sub address{2} 0 7
).
    + inline {1}; auto => /> &1 &2 H0 H1 H2 H3 H4.
      rewrite !ultE => H5 H6 H7 H8 H9 H10 H11. 
      split.
        - apply (eq_from_nth witness); rewrite !size_sub // => j?.
          rewrite !nth_sub //= !get_setE // ifF 1:/#.
          smt(sub_k).
        - apply (eq_from_nth witness); rewrite !size_sub // => j?.
          rewrite !nth_sub //= !get_setE //.
          case (j = 6) => ?; smt(@W32 pow2_32 sub_k).
  
seq 4 2 : (
    #pre /\ 
    to_list buf1{1} = val pk_i{2} ++ val tmp{2}
).
    + sp. 
      ecall {1} (memcpy_u8u8_2_64_2144_post wots_pk1{1} offset_in{1}).
      skip => /> &1 &2 H0 H1 H2 H3.
      rewrite !ultE => H4 H5 H6 H7 H8 H9 H10 H11.
      do split.
        - rewrite to_uintM of_uintK /#.
        - rewrite !to_uintM of_uintK /#.
        - rewrite to_uintD to_uintM of_uintK /#.
        - rewrite !to_uintD !to_uintM of_uintK /#.
        - move => H12 H13 H14 H15 result ->.
          apply (eq_from_nth witness); first by rewrite size_sub // size_cat !valP n_val.
          rewrite size_sub // => j?. 
          case (0 <= j < 32) => [[_?] | ?].
             * rewrite nth_cat valP n_val ifT //.        
               rewrite nth_sub // /EncodeWotsPk insubdK.
               + rewrite /P size_map size_chunk 1:/# size_to_list /#.
               rewrite (nth_map witness).
               + rewrite size_chunk 1:/# size_to_list /#.
               rewrite insubdK.
               + rewrite /P /chunk nth_mkseq /=; first by rewrite size_to_list /#.
               rewrite size_take 1:/# /= size_drop // 1:/# size_to_list /#.
               rewrite /chunk nth_mkseq /=; first by rewrite size_to_list /#.          
               rewrite nth_take 1,2:/# nth_drop 1,2:/# get_to_list n_val.
               congr.
               rewrite !to_uintM of_uintK /#.
             * rewrite nth_cat valP n_val ifF 1:/#.        
               rewrite nth_sub // /EncodeWotsPk insubdK.
               + rewrite /P size_map size_chunk 1:/# size_to_list /#.
               rewrite (nth_map witness).
               + rewrite size_chunk 1:/# size_to_list /#.
               rewrite insubdK.
               + rewrite /P /chunk nth_mkseq /=; first by rewrite size_to_list /#.
               rewrite size_take 1:/# /= size_drop // 1:/# size_to_list /#.
               rewrite /chunk nth_mkseq /=; first by rewrite size_to_list /#.          
               rewrite nth_take 1,2:/# nth_drop 1,2:/# get_to_list n_val.
               congr.
               rewrite !to_uintM of_uintK /#.
   
seq 1 1 : (
    #{/~to_list buf1{1} = val pk_i{2} ++ val tmp{2}}pre /\ 
    to_list buf0{1} = val pk_i{2}
).
    + exists * pk_i{2}, tmp{2}, pub_seed1{1}, addr1{1}, address{2}.
      elim * => P0 P1 P2 P3 P4.
      call (rand_hash_results P0 P1 P2 P3 P4) => [/# |].
      skip => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12.
      do split.
         - smt(merge_nbytes_val).
         - rewrite -H0; smt(@NBytes).
         - smt(sub_k).
         - move => H13 H14 H15 resL resR H17 H16.
           split.
            * apply (eq_from_nth witness); rewrite !size_sub // => j?.
              rewrite !nth_sub //; smt(sub_k).
            * rewrite -H11.
              apply (eq_from_nth witness); rewrite !size_sub // => j?.
              rewrite !nth_sub // H16 /#.

wp; sp.
 

ecall {1} (memcpy_offset_1 offset_out{1} buf0{1}).
auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12.
do split.
- rewrite to_uintM /#.
- rewrite to_uintM /#.
- move => ?? result H13. 
  do split.
   + admit.
   + apply (eq_from_nth witness); first by rewrite size_put !valP.
     admit.
   + smt(sub_N).
   + rewrite to_uintD /#.
   + smt().
   + smt().
   + rewrite ultE to_uintD /#.
   + rewrite ultE to_uintD /#.

(* ------------------------------------------------------------------------------- *)
(*                                                                                 *)
(* ------------------------------------------------------------------------------- *)

seq 2 0 : (t{1} <> W64.zero <=> _len{2} %% 2 = 1).
    + auto => /> &1 &2 *; smt(and_1_mod_2).

wp.

if {1}.


search 


qed.
