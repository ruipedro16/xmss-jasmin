pragma Goals : printall.

require import AllCore List RealExp IntDiv Distr DList IntDiv.
from Jasmin require import JModel JArray.

require import Types Params Parameters Address Notation Hash Primitives Wots XMSS_Commons.
require import XMSS_IMPL.

require import Repr. 
require import Util Utils.

require import Array4 Array8 Array32 Array64 Array68 Array96 Array132 Array136 Array352 Array2144.
require import WArray32 WArray96 WArray136.

require import Correctness_Address Correctness_Mem Correctness_Hash.
require import Utils DistrUtils.

require import BitEncoding.
(*---*) import BitChunking.

require import StdBigop. 
(*---*) import Bigint.

require import Termination.

lemma ltree_correct (_pk : W8.t Array2144.t, _pub_seed : W8.t Array32.t, _addr : W32.t Array8.t) : 
    len = XMSS_WOTS_LEN /\ 
    n = XMSS_N =>
    equiv [
      M(Syscall).__l_tree ~ LTree.ltree :

      size pk{2} = len /\  
      (forall (t0 : W8.t list), t0 \in pk{2} => size t0 = 32) /\
      _addr.[5] = W32.zero /\

      arg{1}.`2 = _pk /\
      arg{1}.`3 = _pub_seed /\
      arg{1}.`4 = _addr /\
      arg{2} = (EncodeWotsPk _pk, _addr, to_list _pub_seed)
      ==>
      to_list res{1}.`1 = res{2}.`1 /\ (* wots pk *)
      res{1}.`3 = res{2}.`2 (* address *)
    ].
proof. 
rewrite /XMSS_WOTS_LEN /XMSS_N.
move => [#] len_val n_val.
proc. 
auto => />.
seq 6 3 : (
  addr{1} = address{2} /\
  pk{2} = EncodeWotsPk wots_pk{1} /\
  _seed{2} = to_list pub_seed{1} /\
  _len{2} = to_uint l{1} /\
  _len{2} = 67 /\
  size pk{2} = len /\
  (forall (t0 : W8.t list), t0 \in pk{2} => size t0 = 32) /\
  height{1} = W32.zero /\
  address{2}.[5] = height{1}
); first by inline {1}; auto. 

seq 1 1 : (
  addr{1} = address{2} /\
  (forall (k : int), 0 <= k < 32 => wots_pk{1}.[k] = nth witness (nth witness pk{2} 0) k) /\ (* The first chunk is equal *)
  size pk{2} = len /\
  (forall (t0 : W8.t list), t0 \in pk{2} => size t0 = 32)
); last first.
    + ecall {1} (_x_memcpy_u8u8_post tmp{1}).
      auto => /> &1 &2 H0 *.  
      have E : forall (k : int), 0 <= k && k < len => size (nth witness pk{2} k) = 32 by smt(@List). 
      apply (eq_from_nth witness); [by rewrite size_to_list E /# |]. 
      rewrite size_to_list => j?. 
      rewrite -H0 //= initiE //=.

conseq (: _ ==>
  addr{1} = address{2} /\
  (forall (k : int), 0 <= k < 32 =>  wots_pk{1}.[k] = nth witness (flatten pk{2}) k) /\
  size pk{2} = len /\ 
  (forall (t0 : W8.t list), t0 \in pk{2} => size t0 = 32)
).
    + auto => /> &1 &2 ???? pkL pkR H4 H5 H6 k??. 
      rewrite -nth_flatten.
         * rewrite H5 len_val //=.                      
         * rewrite (: size (nth witness pkR 0) = 32) //= H6 //=; smt(@List). 
         * rewrite H4 //=; congr. 
           rewrite sumzE BIA.big_map /(\o) //= -(StdBigop.Bigint.BIA.eq_big_seq (fun _ => 32)) 1:#smt:(@List) big_constz count_predT. 
           rewrite size_take //= ifT 1:/# //=.

(* ------------------------------------------------------------------------------- *)
(*                     At this point, we only have the while loop                  *)
(* ------------------------------------------------------------------------------- *)

while (
  addr{1} = address{2} /\
  _seed{2} = to_list pub_seed{1} /\
  
  size pk{2} = len /\
  (forall (t0 : W8.t list), t0 \in pk{2} => size t0 = 32) /\

  1 <= to_uint l{1} <= 67 /\
  _len{2} = to_uint l{1} /\
  
  pk{2} = EncodeWotsPk wots_pk{1} /\ 
  address{2}.[5] = height{1}
); last first.
    + auto => /> *; do split;1..3:smt().
        * smt(@W64). 
        * move => *.
          rewrite /EncodeWotsPk (nth_flatten witness 32); [rewrite size_all_r 1:#smt:(@BitChunking @List) |]. 
          rewrite /chunk size_to_list nth_mkseq 1:/# => />.
          rewrite nth_take //= 1:/# nth_drop //= 1,2:/#.
          congr => /#. 

(* ------------------------------------------------------------------------------- *)
(*              The first subgoal of the outter while loop starts here             *)
(* ------------------------------------------------------------------------------- *)
 
(* This removes the addresses at the end *)
seq 7 4 : (
  addr{1} = address{2} /\
  _seed{2} = to_list pub_seed{1} /\
  size pk{2} = len /\
  (forall (t0 : W8.t list), t0 \in pk{2} => size t0 = 32) /\
  1 <= to_uint l{1} <= 67 /\
  _len{2} = to_uint l{1} /\ 
  pk{2} = EncodeWotsPk wots_pk{1} /\ 
  address{2}.[5] = height{1} 
); last first.  
    + inline {1}. auto => /> &1 &2 *; do split. 
        * rewrite /get_tree_height /set_tree_height; congr ; smt(@W32). 
        * rewrite /get_tree_height /set_tree_height get_setE //=; smt(@W32).
        * rewrite ultE (: to_uint W64.one = 1) /#.        
        * rewrite ultE (: to_uint W64.one = 1) /#.        

seq 2 0 : (#pre /\ to_uint parent_nodes{1} = to_uint l{1} %/ 2).
    + by auto => /> *; rewrite truncate_1_and_63 shr_1.
 
seq 2 2 : (
  addr{1} = address{2} /\
  _seed{2} = to_list pub_seed{1} /\
  size pk{2} = len /\
  (forall (t0 : W8.t list), t0 \in pk{2} => size t0 = 32) /\
  pk{2} = EncodeWotsPk wots_pk{1} /\
  _len{2} = to_uint l{1} /\
  address{2}.[5] = height{1} /\
  1 <= to_uint l{1} <= 67 /\ _len{2} = to_uint l{1} /\ 
  to_uint parent_nodes{1} = to_uint l{1} %/ 2
); last first.
    + seq 2 0 : (#pre /\ t{1} = l{1} `&` W64.one); first by auto.
      if; 3: by admit.
        * auto => /> &1 &2 *; smt(and_1_mod_2). 
        * seq 3 0 : (#pre /\ offset_out{1} = (l{1} `>>` W8.one) * W64.of_int 32); first by auto => /> &1 *; rewrite truncate_1_and_63.
          seq 3 0 : (#pre /\ offset_in{1}  = (l{1} - W64.one) * W64.of_int 32); first by auto => />.
          seq 1 2 : (#pre).
           - inline {1}. wp; sp. 
             while {1}
             (
               addr{1} = address{2} /\
               _seed{2} = to_list pub_seed{1} /\
               size pk{2} = len /\
               (forall (t0 : W8.t list), t0 \in pk{2} => size t0 = 32) /\
               pk{2} = EncodeWotsPk wots_pk{1} /\
               _len{2} = to_uint l{1} /\
               address{2}.[5] = height{1} /\
               1 <= to_uint l{1} <= 67 /\
               _len{2} = to_uint l{1} /\ 
               to_uint parent_nodes{1} = to_uint l{1} %/ 2 /\
               t{1} = l{1} `&` W64.one /\
               t{1} <> W64.zero /\
               offset_out{1} = (l{1} `>>` W8.one) * (of_int 32)%W64 /\
               offset_in{1} = (l{1} - W64.one) * (of_int 32)%W64 /\
        
               0 <= i0{1} <= 32 /\
               forall (k : int), 0 <= k < i0{1} => out{1}.[to_uint offset_out{1} + i0{1}] = out{1}.[to_uint offset_in{1} + i0{1}]
         )
         (32 - i0{1}); last first.
              * auto => /> &1 H0 *; split => [/# | i0 outL]; split => [/# | ???].
                have ->: i0 = 32 by smt(). 
                move => H; split; [by rewrite size_put H0 |].
                split. 
                      - admit. (* lemma all_put *)
                      - apply (eq_from_nth witness); [by rewrite size_put /EncodeWotsPk !size_chunk //= !size_to_list //= |]. 
                        rewrite size_put H0 len_val => i Hi. 
                        rewrite /EncodeWotsPk /chunk nth_mkseq; [by rewrite size_to_list /# |]. 
                        rewrite nth_put; [by rewrite /_floor_2 shr_1 of_uintK size_mkseq size_to_list (: max 0 (2144 %/ 32) = 67) /# |]. 
                        do 2! (rewrite nth_mkseq; [by rewrite size_to_list /# |]). 
                        auto => />. 
                        admit.          

              * auto => /> &hr *; do split;1,2,4:smt(). 
                move => k??. rewrite get_setE.
                      - split; [smt(@W64 pow2_64) |]. move => ?. admit. 
                rewrite to_uintM shr_1 of_uintK (: (32 %% W64.modulus) = 32) 1:/#.
                admit. 
           - auto => /> &1 *.  
             have E0: to_uint l{1} %% 2 <> 0 by smt(and_1_mod_2).
             do split.  
                + rewrite truncate_1_and_63 to_uintD shr_1 (: to_uint W64.one = 1) /#.
                + rewrite truncate_1_and_63 to_uintD shr_1 (: to_uint W64.one = 1) /#.
                + rewrite truncate_1_and_63 to_uintD shr_1 (: to_uint W64.one = 1) 1:/#. 
                  rewrite /_ceil_2 /is_even ifF 1:/# shr_1 of_uintK. 
                  have ->: to_uint l{1} %% W64.modulus = to_uint l{1} by smt(). 
                  have ->: (to_uint l{1} %/ 2 + 1) %% W64.modulus = to_uint l{1} %/ 2 + 1 by smt(). 
                  reflexivity.
        * auto => /> &1 *.
          have E0: to_uint l{1} %% 2 = 0 by smt(and_1_mod_2).
          do split.
           - rewrite truncate_1_and_63 shr_1 /#.
           - rewrite truncate_1_and_63 shr_1 /#.
           - rewrite truncate_1_and_63 shr_1 /_ceil_2 to_uintK shr_1 /is_even ifT //=.              

(* ------------------------------------------------------------------------------- *)
(*                         The inner while loop starts here                        *)
(* ------------------------------------------------------------------------------- *)
while (
  0 <= i{2} <= _floor_2 _len{2} /\
  i{2} = to_uint i{1} /\
  address{2} = addr{1} /\
  size pk{2} = len /\
  pk{2} = EncodeWotsPk wots_pk{1} /\
  (forall (t0 : W8.t list), t0 \in pk{2} => size t0 = 32) /\
  _seed{2} = to_list pub_seed{1} /\
  address{2}.[5] = height{1} /\
  1 <= to_uint l{1} <= 67 /\ _len{2} = to_uint l{1} /\ 
  to_uint parent_nodes{1} = to_uint l{1} %/ 2
); last first. 
    + auto => /> &1 *. do split.  
       * rewrite /_floor_2 shr_1 to_uintK /#.
       * rewrite ultE (: to_uint W64.zero = 0 ) 1:/# => H.
         rewrite /_floor_2 shr_1 to_uintK /#.
       * rewrite /_floor_2 shr_1 to_uintK => H. 
         rewrite ultE (: to_uint W64.zero = 0) 1:/# /#.

seq 2 1 : (#pre); first by inline {1}; auto => />. 

seq 3 0 : (
  #pre /\ 
  offset_in{1} = i{1} * W64.of_int 64 /\
  bytes{1} = W64.of_int 64
); first by  auto => /> *; ring. 

seq 1 2 : (#pre /\ to_list buf1{1} = pk_i{2} ++ tmp{2}).
    + admit.

seq 1 1 : (
  0 <= _len{2} <= 67 /\
  0 <= i{2} <= _floor_2 _len{2} /\
  i{2} = to_uint i{1} /\
  address{2} = addr{1} /\
  size pk{2} = len /\
  pk{2} = EncodeWotsPk wots_pk{1} /\
  (forall (t0 : W8.t list), t0 \in pk{2} => size t0 = 32) /\
  _seed{2} = to_list pub_seed{1} /\ 
  address{2}.[5] = height{1} /\
  1 <= to_uint l{1} <= 67 /\ _len{2} = to_uint l{1} /\ 
  to_uint parent_nodes{1} = to_uint l{1} %/ 2 /\

  to_list buf0{1} = pk_i{2} 
).
    + admit. 

seq 2 1 : (#pre). 
    + admit. 

auto => /> &1 ??? H0 ????H1.
have := H0.
rewrite /_floor_2 shr_1 of_uintK (: to_uint l{1} %% W64.modulus  = to_uint l{1}) 1:/# => H3. 
do split. 
    + smt().
    + move => ?. admit. (* This is false *)
    + smt(@W64 pow2_64). 
    + rewrite ultE to_uintD_small 1:#smt:(@W64) (: to_uint W64.one = 1) 1:/# H1 //=. 
    + rewrite ultE to_uintD_small 1:#smt:(@W64) (: to_uint W64.one = 1) 1:/# H1 //=. 
qed.
