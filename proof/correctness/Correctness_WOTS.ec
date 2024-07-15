pragma Goals : printall.

require import AllCore List RealExp IntDiv.
from Jasmin require import JModel JArray.

require import Params Parameters Address Notation Primitives Wots Generic.
require import RandomBytes XMSS_IMPL XMSS_IMPL_HOP1.

require import Array2 Array3 Array8 Array32 Array67 Array2144.

require import Utils. (* valid ptr predicate *)
require import Correctness_Mem. (* memcpy results *)
(*---*) import NBytes.

type adrs = W32.t Array8.t.

(* require import Correctness_Hash. *)


lemma addr_to_bytes_post (x : W32.t Array8.t) :
    hoare [M_Hop1(Syscall).__addr_to_bytes : arg.`2 = x ==> to_list res = toByte (W32.of_int 1) 32].
proof.
proc.
admit.
qed.

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

(*

op decode_wots_sk (sk_spec : wots_sk) : W8.t Array2144.t =
  Array2144.of_list witness (flatten sk_spec).

pred first_nth_equal (a : W8.t Array2144.t) (b : W8.t list) (n : int) =
take n (to_list a) = take n b.

lemma expand_seed_correct (_in_seed : W8.t Array32.t,
                           _pub_seed : W8.t Array32.t, _addr : W32.t Array8.t):
    len = XMSS_WOTS_LEN =>
    equiv [M_Hop1(Syscall).__expand_seed ~ WOTS.pseudorandom_genSK :
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
  + inline; auto => />.
seq 1 0 : (#pre /\ aux{1} = pub_seed{1}).
    + ecall {1} (_x_memcpy_u8u8_post_hop1 pub_seed{1}); auto => />.
while (
  len{2} = 67 /\
  ={i} /\ 0 <= i{1} <= 67 /\
  addr{1} = address{2} /\
  seed{2} = to_list _pub_seed /\
  first_nth_equal outseeds{1}(flatten sk{2}) (i{1} * 32) (* Same as i*N *)
); last first.
    + auto => /> &1 &2 *. do split.
      * admit.
      * by rewrite len_val.
      * move => *. rewrite /decode_wots_sk. admit.
    + seq 1 1 : (#pre); 1:inline;auto.
      * auto => />. admit.
      (* auto => /> &1 &2 *; do split; 1,2,4,5:smt(). admit. *)
qed.
*)

(*---*) import NBytes.

op address_to_bytes (x : adrs) : W8.t list. (* TODO: Specify this and prove equivalence *)

lemma addr_to_bytes__post (x : W32.t Array8.t) :
    phoare[M_Hop1(Syscall).__addr_to_bytes : arg.`2 = x ==> to_list res = address_to_bytes x] = 1%r.
proof.
proc.
admit.
qed.

module HopA = {
  proc pseudorandom_genSK(sk_seed : nbytes, seed : nbytes, address : adrs) : W8.t list * adrs= {
    var sk : W8.t list <- nseq 2144 witness;
    var sk_i : nbytes;
    var key : nbytes;
    var i : int;
    
    address <- set_hash_addr address 0;
    address <- set_key_and_mask address 0;

    i <- 0;
    while (i < len) {
      address <- set_chain_addr address i;
      key <- address_to_bytes address;
      sk_i <- PRF_KEYGEN sk_seed address key;
      sk <- mkseq (fun i_0 => if 32 <= i_0 < 32 + 32 then nth witness sk_i i_0 else nth witness sk i_0) 2144;
      i <- i + 1;
    }

    return (sk, address);
  }
}.

lemma expand_seed_correct_hopA (_in_seed : W8.t Array32.t,
                           _pub_seed : W8.t Array32.t, _addr : W32.t Array8.t):
    len = XMSS_WOTS_LEN =>
    equiv [M_Hop1(Syscall).__expand_seed ~ HopA.pseudorandom_genSK :
      arg{1}.`2 = _in_seed /\ 
      arg{1}.`3 = _pub_seed /\
      arg{1}.`4 = _addr /\
      arg{2} = (to_list _in_seed, to_list _pub_seed, _addr) ==>
      res{2}.`1 = to_list res{1}.`1 /\ 
      res{2}.`2 = res{1}.`2].
proof.
rewrite /XMSS_WOTS_LEN => len_val.
proc.
seq 2 1 : (#pre); 1:auto => />.
seq 2 2 : (
  seed{2} = to_list pub_seed{1} /\
  sk_seed{2} = to_list inseed{1} /\
  address{2} = addr{1}
); 1:inline; auto => />; rewrite /set_hash_addr /set_key_and_mask. 
seq 1 0 : (#pre /\ aux{1} = pub_seed{1}).
    + ecall {1} (_x_memcpy_u8u8_post_hop1 pub_seed{1}); auto => />.
while (
  len{2} = 67 /\
  ={i} /\ 0 <= i{1} <= 67 /\
  addr{1} = address{2} /\
  seed{2} = to_list pub_seed{1} /\
  (forall (k : int), 0 <= k < i{2} * 32 => (nth witness sk{2} k) = outseeds{1}.[k])
). (* 2144 = 67 * 32 = len1 * n *)
(* First subgoal of while *)
    + auto => />. move => &1 &2 *; do split.
        * smt().
        * smt().
        * smt().
        * smt().
        * smt().
        * smt().
        * auto => /> k *. rewrite nth_mkseq 1:/#. auto => />. case (32 <= k && k < 64).
             - move => *. admit. (* Need lemma about PRF_KEYGEN *)
             - move => *. admit.
        * smt().
        * smt().
        * inline M_Hop1(Syscall).__set_chain_addr. sp.
          seq 1 1 : (#pre /\ to_list aux{1} = address_to_bytes addr{1}).
             + ecall {1} (addr_to_bytes__post addr{1}); auto => />.
          skip => /> &1 &2 *. do split.
             + smt().
             + smt().
             + move => *. rewrite nth_mkseq 1:/#. admit.
             + smt().
             + smt().
(* Second subgoal of while *)
    + auto => /> &1 &2 *. do split. smt(). smt().
      move => out_L i out_R ?? _ ?? k. 
      admit.
qed.


op load_mem_w8_array32 (mem : global_mem_t) (ptr : W64.t) : W8.t Array32.t = 
  Array32.init (fun i => loadW8 mem (to_uint ptr + i)).

op load_mem_w8_list32 (mem : global_mem_t) (ptr : W64.t) : W8.t list =
  mkseq (fun i => loadW8 mem (to_uint ptr + i)) 32.

lemma gen_chain_inplace_correct (buf : W8.t Array32.t, _start_ _steps_ : W32.t, _addr_ : W32.t Array8.t, _pub_seed_ : W8.t Array32.t) :
    w = XMSS_WOTS_W /\ len = XMSS_WOTS_LEN =>
    equiv [M_Hop1(Syscall).__gen_chain_inplace ~ Chain.chain : 
      arg{1}= (buf, _start_, _steps_, _pub_seed_, _addr_) /\
      arg{2} = (to_list buf, to_uint _start_, to_uint _steps_, to_list _pub_seed_, _addr_) /\
      0 <= to_uint _start_ /\
      0 <= to_uint _steps_ /\
      0 <= to_uint (_start_ + _steps_) <= XMSS_WOTS_W - 1  ==> 
        res{2}.`1 = to_list res{1}.`1 /\ res{1}.`2 = res{2}.`2].
proof.
rewrite /XMSS_WOTS_W /XMSS_WOTS_LEN; move => [w_val len_val].
proc; auto => />.
while (
  0 <= to_uint _start_ /\
  0 <= to_uint _steps_ /\
  0 <= to_uint (_start_ + _steps_) && to_uint (_start_ + _steps_) <= 15 /\
  start{2} = to_uint start{1} /\ t{2} = to_list out{1}
).



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
