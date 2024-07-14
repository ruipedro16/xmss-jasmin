pragma Goals : printall.

require import AllCore List RealExp IntDiv.
from Jasmin require import JModel JArray.

require import Params Parameters Address Notation Primitives Wots Generic.
require import RandomBytes XMSS_IMPL XMSS_IMPL_HOP1.

require import Array2 Array3 Array8 Array32 Array67 Array2144.

require import Utils. (* valid ptr predicate *)
(* require import Correctness_Hash. *)

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
        * auto => /> &1 &2 *; do split.
            - smt(@W64).
            - smt(@W64 pow2_64).
            - smt(size_put).
            - smt(@W64 pow2_64).
            - smt(@W64 pow2_64).
            - smt(@W64 pow2_64).
            - smt(@W64 pow2_64).
            - smt(@W64 pow2_64).
            - rewrite logw_val //. smt(@W64 pow2_64 @IntDiv).
            - smt(@W64 pow2_64).
            - smt(@W64 pow2_64 @IntDiv).
            - move => j Hj *. rewrite get_setE 1:/# //= nth_put ; 1:smt(size_nseq).
              case (j = to_uint out{1}); last first.
                + move => *. rewrite ifF. smt(). smt(@W64).
                + move => -> //=. rewrite logw_val w_val /=. 
                  have -> : 15 = 2 ^ 4 - 1 by smt().
                  rewrite and_mod // and_mod // shr_div shr_div //=. 
                  have -> : 31 = 2 ^ 5 - 1 by smt().
                  rewrite and_mod //= to_uint_truncateu8 to_uint_zeroextu32 //=. 
                  smt(@W64 @W8 @W32 pow2_32 pow2_64 pow2_8 @IntDiv).
        * auto => /> &1 &2 *; do split.
            - smt(@W64).
            - smt(@W64 pow2_64).
            - smt(size_put).
            - smt(@W64 pow2_64).
            - smt(@W64 pow2_64).
            - smt(@W64 pow2_64).
            - smt(@W64 pow2_64).
            - rewrite logw_val //= to_uintB. smt(@W64). smt(@W64 pow2_64).
            - rewrite logw_val //. smt(@W64 pow2_64 @IntDiv).
            - smt(@W64 pow2_64 @IntDiv).
            - move => j Hj *. rewrite get_setE 1:/# //= nth_put ; 1:smt(size_nseq).
              case (j = to_uint out{1}); last first. 
                + move => *. rewrite ifF. smt(). smt(@W64).
                + move => -> //=. rewrite logw_val w_val /=. 
                  have -> : 15 = 2 ^ 4 - 1 by smt().
                  rewrite and_mod // and_mod // shr_div shr_div //=. 
                  have -> : 31 = 2 ^ 5 - 1 by smt().
                  rewrite and_mod //= to_uint_truncateu8 to_uint_zeroextu32 //=. 
                  rewrite to_uintB. smt(@W64). simplify. 
                  smt(@W64 @W8 @W32 pow2_32 pow2_64 pow2_8 @IntDiv).
(* Last subgoal of while *)
    + skip => /> *; do split.
        * smt(size_nseq).
        * smt(@W64 pow2_64).
        * smt(@W64 pow2_64).
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
        * auto => /> &1 &2 *; do split; 1..11:smt(@W64 @IntDiv pow2_64 size_put).
          move => j *.  rewrite get_setE 1:/# //= nth_put ; 1:smt(size_nseq).
          case (j = to_uint out{1}); last first. 
            + move => *. rewrite ifF 1:/#. smt(@W64).
            + move => -> //=. rewrite logw_val w_val /=. have -> : 15 = 2 ^ 4 - 1 by smt().
              rewrite and_mod // and_mod // shr_div shr_div //=. 
              have -> : 31 = 2 ^ 5 - 1 by smt().
              rewrite and_mod //= to_uint_truncateu8 to_uint_zeroextu32 //=. 
              smt(@W64 @W8 @W32 pow2_32 pow2_64 pow2_8 @IntDiv).
        * auto => /> &1 &2 *; do split; 1..7,9,10:smt(@W64 @IntDiv pow2_64 size_put).
            + rewrite logw_val //= to_uintB; smt(@W64 pow2_64).
            + move => j Hj *. rewrite get_setE 1:/# //= nth_put ; 1:smt(size_nseq).
              case (j = to_uint out{1}); last first. 
                - move => *. rewrite ifF 1:/#. smt(@W64).
                - move => -> //=. rewrite logw_val w_val /=. 
                  have -> : 15 = 2 ^ 4 - 1 by smt().
                  rewrite and_mod // and_mod // shr_div shr_div //=. 
                  have -> : 31 = 2 ^ 5 - 1 by smt().
                  rewrite and_mod //= to_uint_truncateu8 to_uint_zeroextu32 //=. 
                  rewrite to_uintB; 1:smt(@W64). simplify.
                  smt(@W64 @W8 @W32 pow2_32 pow2_64 pow2_8 @IntDiv).
(* Second subgoal of while *)
    + skip => /> &1. do split; 2,3:smt(@W64 pow2_64). smt(size_nseq).
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
); last first.
    + by auto => /> /#.
    + auto => /> &1 Hmsg Hcsum0 Hcsum1 Hi0 _. 
      rewrite /(\ult) of_uintK /= => Hlt Hi1.
      rewrite to_uintD to_uintB.
        * by rewrite /(\ule) /= to_uint_zeroextu64 1:/#.
      rewrite !of_uintK /= modz_small 1:/# modz_small 1:/#.
      have -> : nth witness (map W32.to_uint (to_list msg)) (to_uint i{1}) = to_uint (zeroextu64 msg.[to_uint i{1}]).
        * rewrite to_uint_zeroextu64 (nth_map witness).
            -  by rewrite size_to_list /#.
            -  smt().
      by rewrite !to_uint_zeroextu64 to_uintD_small /= /#.
qed.





(************************************************************************************)





op decode_wots_sk (sk_spec : wots_sk) : W8.t Array2144.t =
  Array2144.of_list witness (flatten sk_spec).

(* Preciso do Encode / Decode do PRF *)
(* Preciso do Encode / Decode do PRF_KEYGEN *)

lemma expand_seed_correct (_in_seed : W8.t Array32.t,
                           _pub_seed : W8.t Array32.t, _addr : W32.t Array8.t):
    len = XMSS_WOTS_LEN =>
    equiv [Mp(Syscall).__expand_seed ~ WOTS.pseudorandom_genSK :
      arg{1}.`2 = _in_seed /\ 
      arg{1}.`3 = _pub_seed /\
      arg{1}.`4 = _addr /\
      arg{2} = (to_list _in_seed, to_list _pub_seed, _addr) ==>
      res{1}.`1 = decode_wots_sk res{2}.`1 /\ 
      res{1}.`2 = res{2}.`2].
proof.
rewrite /XMSS_WOTS_LEN ; move => len_val.
proc.
auto => />.
seq 2 1 : (#pre); 1:auto => />.
seq 2 2 : (
  inseed{1} = _in_seed /\
  pub_seed{1} = _pub_seed /\
  addr{1} = address{2} /\ 
  seed{2} = to_list _pub_seed
).
  + inline. auto => />.
seq 2 0 : (#pre /\ aux{1} = pub_seed{1}).
    + admit.
while (
  len{2} = 67 /\
  ={i} /\ addr{1} = address{2} /\
  sk_i{2} = to_list ith_seed{1} (* /\
  out are equal on both side up to the ith seed 
  *)
).
(* First subgoal of while *)
    + seq 1 1 : (#pre); 1:inline;auto => />.
      admit.
(* Second subgoal of while *)
    + auto => /> &1 &2 *; do split;2:smt().
      * admit.
      * move => *. admit.
qed.

op load_mem_w8_array32 (mem : global_mem_t) (ptr : W64.t) : W8.t Array32.t = 
  Array32.init (fun i => loadW8 mem (to_uint ptr + i)).

op load_mem_w8_list32 (mem : global_mem_t) (ptr : W64.t) : W8.t list =
  mkseq (fun i => loadW8 mem (to_uint ptr + i)) 32.

lemma gen_chain_correct mem (_out_ : W8.t Array32.t, _in_ptr_ : W64.t, _start_ _steps_ :W32.t, 
                             _pub_seed_ :W8.t Array32.t, _addr_ : W32.t Array8.t) :
    len = XMSS_WOTS_LEN /\ w = XMSS_WOTS_W => 
      equiv [M(Syscall).__gen_chain ~ Chain.chain :
       arg{1} = (_out_, _in_ptr_, _start_, _steps_, _pub_seed_, _addr_) /\
       arg{2} = (load_mem_w8_list32 mem _in_ptr_, 
                 to_uint _start_, to_uint _steps_, to_list _pub_seed_, _addr_) /\ 
       0 <= to_uint _start_ <= XMSS_WOTS_W - 1 /\ 
       0 <= to_uint _steps_ <= XMSS_WOTS_W - 1 /\ 
       0 <= to_uint (_start_ + _steps_) <= XMSS_WOTS_W - 1 /\
       valid_ptr _in_ptr_ (W64.of_int 32) ==> 
          res{2}.`1 = to_list res{1}.`1 /\ res{1}.`2 = res{2}.`2].
proof.
rewrite /XMSS_WOTS_LEN /XMSS_WOTS_W; move => [len_val w_val].
proc.
auto => />.
seq {1} 1 0 : (out{1} = load_mem_w8_array32 mem in_ptr{1}).
  + admit.
while (
  #pre /\
  0 <= to_uint i{1} <= to_uint t{1} /\ chain_count{2} = to_uint i{1} /\
  t{1} = start{1} + steps{1} /\
  addr{1} = address{2} /\
  t{2} = to_list out{1}
) ; auto => /> ; last first.
- progress.
    + smt(@W32).
    + rewrite to_uintD. admit. (* smt(@W32). *)
    + admit.
    + admit.
    + admit.
    + admit.
    + rewrite ultE to_uintD. admit.
admit.
(*
- call (thash_f_correct out{1} addr{1}). (* out = t /\ addr = address *)
  call set_hash_addr_correct i.
*)
qed.

lemma gen_chain_inplace_correct (_steps_ : W32.t, _addr_ : W32.t Array8.t, _pub_seed_ : W8.t Array32.t, r : W8.t Array32.t) :
    w = XMSS_WOTS_W /\ len = XMSS_WOTS_LEN =>
    equiv [Mp(Syscall).__gen_chain_inplace ~ Chain.chain : 
      arg{1} = (r, _steps_, _pub_seed_, _addr_) /\
      arg{2} = (to_list r, 0, to_uint _steps_, to_list _pub_seed_, _addr_) /\
      0 <= to_uint _steps_ <= XMSS_WOTS_W - 1  ==> 
        res{2}.`1 = to_list res{1}.`1 /\ res{1}.`2 = res{2}.`2].
proof.
rewrite /XMSS_WOTS_W /XMSS_WOTS_LEN.
move => [w_val len_val].
proc; auto => />.
while(
  #pre /\
  _seed{2} = to_list pub_seed{1} /\
  X{2} = to_list r{1} /\
  i{2} = to_uint i{1} /\ 0 <= to_uint i{1} <= to_uint steps{1} /\
  chain_count{2} = to_uint i{1} /\
  s{2} = to_uint steps{1} /\
  t{2} = to_list out{1} /\
  addr{1} = address{2}
); last first.
- auto => /> &1 &2 *; do split; smt(@W32).
- auto => />. auto => /> &1 &2 *; do split. (* thash_f_ precisa de ser inlined ou de no codigo trocar o sitio onde atualizo o address pela segunda vez pq facilita a prova *)
    + admit. (* preciso de out no invariante *)
    + admit. (* Tenho de tirar o ={addr} da #pre *)
    + admit. (* problema do addr *)
    + admit. (* Preciso do encoding do F *)
    + admit. (* Problema do addr *)
    + admit. (* Nao sei *)
qed.

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
