pragma Goals : printall.

require import AllCore List RealExp IntDiv.
from Jasmin require import JModel JArray.

require import Params Parameters Address Notation Primitives Wots Generic.
require import XMSS_IMPL.

require import Array3 Array8 Array32 Array67 Array2144.

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
conseq (: _ ==> size base_w{2} = 67 /\ forall (k:int), 0 <= k < 67 => to_uint output{1}.[k] = nth witness base_w{2} k ).
  + move => &1 &2 /> *. apply (eq_from_nth witness). rewrite size_map size_to_list /#. 
    move => *. rewrite  (nth_map witness). smt(Array67.size_to_list). rewrite get_to_list /#.  
sp.
(* unroll {1} 1 ; unroll {2} 1. 
if; 1:smt().
rcondt {1} 1; auto.
rcondt {2} 1; auto.
seq 10 8 :  (
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
            (forall (j : int), 0 <= j < to_uint out{1} => (to_uint output{1}.[j]) = nth witness base_w{2} j)).
auto => /> &1 * ; split.
              + rewrite size_put size_nseq //.
              + split; first by rewrite logw_val. split. smt(). 
move => j *. have -> : j=0 by smt(). rewrite get_setE 1:/# //= nth_put ; 1:smt(size_nseq).
                simplify. rewrite logw_val w_val /=. have -> : 15 = 2 ^ 4 - 1 by smt().
                rewrite and_mod // and_mod // shr_div shr_div //=. have -> : 31 = 2 ^ 5 - 1 by smt().
                rewrite and_mod //= to_uint_truncateu8 to_uint_zeroextu32 //=. 
                smt(@W64 @W8 @W32 pow2_32 pow2_64 pow2_8 @IntDiv).
*)
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
if. 
auto => /> &1 &2 *; smt(@W64).
auto => /> &1 &2 *. do split.
smt(@W64).
          smt(@W64 pow2_64).
          smt(size_put).
smt(@W64 pow2_64).
          smt(@W64 pow2_64).
          smt(@W64 pow2_64).
          smt(@W64 pow2_64).
          smt(@W64 pow2_64).
          rewrite logw_val //. smt(@W64 pow2_64 @IntDiv).
            smt(@W64 pow2_64).
          smt(@W64 pow2_64 @IntDiv).
move => j Hj *. 
rewrite get_setE 1:/# //= nth_put ; 1:smt(size_nseq).
case (j = to_uint out{1}); last first. move => *.
rewrite ifF. smt().
smt(@W64).
move => -> //=.
rewrite logw_val w_val /=. have -> : 15 = 2 ^ 4 - 1 by smt().
                rewrite and_mod // and_mod // shr_div shr_div //=. have -> : 31 = 2 ^ 5 - 1 by smt().
                rewrite and_mod //= to_uint_truncateu8 to_uint_zeroextu32 //=. 
                smt(@W64 @W8 @W32 pow2_32 pow2_64 pow2_8 @IntDiv).
auto => /> &1 &2 *. do split.
smt(@W64).
          smt(@W64 pow2_64).
          smt(size_put).
smt(@W64 pow2_64).
          smt(@W64 pow2_64).
          smt(@W64 pow2_64).
          smt(@W64 pow2_64).
          rewrite logw_val //= to_uintB.  smt(@W64).
       smt(@W64 pow2_64).
          rewrite logw_val //. smt(@W64 pow2_64 @IntDiv).
          
          smt(@W64 pow2_64 @IntDiv).
move => j Hj *. 
rewrite get_setE 1:/# //= nth_put ; 1:smt(size_nseq).
case (j = to_uint out{1}); last first. move => *.
rewrite ifF. smt().
smt(@W64).
move => -> //=.
rewrite logw_val w_val /=. have -> : 15 = 2 ^ 4 - 1 by smt().
                rewrite and_mod // and_mod // shr_div shr_div //=. have -> : 31 = 2 ^ 5 - 1 by smt().
                rewrite and_mod //= to_uint_truncateu8 to_uint_zeroextu32 //=. 
rewrite to_uintB.
smt(@W64).
simplify.

smt(@W64 @W8 @W32 pow2_32 pow2_64 pow2_8 @IntDiv).
skip => /> &1. do split.
smt (size_nseq).
smt(@W64 pow2_64).
smt(@W64 pow2_64).
qed.

lemma wots_checksum_correctness (msg : W32.t Array67.t) :
    len1 = XMSS_WOTS_LEN1 /\  w = XMSS_WOTS_W =>
    equiv [M(Syscall).__csum ~ WOTS.checksum :
      (forall (k : int), 0 <= k < 67 => 0 <= to_uint msg.[k] <= (w - 1)) /\
      arg{1} = msg /\ arg{2} = mkseq (fun i => to_uint msg.[i]) 67  ==> to_uint res{1} = res{2}].
proof.
rewrite /XMSS_WOTS_LEN1 /XMSS_WOTS_W ; move => [len1_val w_val].
proc => /=.
while (
  #pre /\
  to_uint csum{1} = checksum{2} /\ 0 <= to_uint csum{1} < (len1 * (w - 1) * 2^8) /\
  i{2} = to_uint i{1} /\ m{2} = mkseq (fun i => to_uint msg_base_w{1}.[i]) 67 /\
  0 <= i{2} <= len1
); last by auto => /> /#.
auto => /> &1 &2 * ; do split; 2,4,5,6,7,8: smt(@W64 pow2_64).
    + have E: nth witness (mkseq (fun (i0 : int) => to_uint msg.[i0]) 67) (to_uint i{1}) = to_uint (JWord.W2u32.zeroextu64 msg.[to_uint i{1}]). print mkseq.
        * admit. (* smt. / smt(@JWord) used to work but now it doesnt *)
      rewrite w_val E //=. admit.
    + move => *. rewrite len1_val w_val //=. admit.
qed.

lemma expand_seed_correct :
    len = XMSS_WOTS_LEN =>
    equiv [Mp(Syscall).__expand_seed ~ WOTS.pseudorandom_genSK : true ==> true].
proof.
rewrite /XMSS_WOTS_LEN ; move => len_val.
proc.
inline Mp(Syscall).__set_hash_addr Mp(Syscall).__set_key_and_mask Mp(Syscall).__set_chain_addr.
while (
  len{2} = 67 /\
  ={i} /\ 0 <= i{1} <= 67 /\
  addr{1} = address{2} /\
  aux_list{1} = sk_i{2}
) ; auto => />.
- admit.
- admit.
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
proc.
while(
  #pre /\
  0 <= to_uint i{1} <= to_uint steps{1} /\
  chain_count{2} = to_uint i{1} /\
  s{2} = to_uint steps{1} /\
  t{2} = to_list out{1} /\
  addr{1} = address{2}
); auto => />.
- move => &1 &2 * ; do split.
    + admit.
    + smt().
    + smt().
    + admit.
    + smt().
    + smt().
    + smt().
    + smt().
    + admit.
    + smt().
    + smt().
    + smt().
    + smt().
    + smt().
    + smt().
    + smt().
    + smt().
    + smt().
    + smt().
- inline Mp(Syscall).__thash_f_ Mp(Syscall)._thash_f. admit. (* call thash_f_correct. : FIXME CANNOT INFER ALL PLACEHOLDERS *)
- move => * ; do split ; smt(@W32).
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
swap {1} 1 1 ; sp.
while (
  0 <= i{1} <= 32 /\ ={i} /\
  address{2} = addr{1} /\
  (forall (k : int), 0 <= k < (32 * i{1}) => pk{1}.[k] = nth witness (flatten pk{2}) k)
) ; auto => />.
+ progress. admit.
+ inline Mp(Syscall).__set_chain_addr Mp(Syscall).__gen_chain_inplace_ Mp(Syscall)._gen_chain_inplace. 
  wp ; sp. (* call gen_chain_inplace_correct. : CANNOT INFER ALL PLACEHOLDERS*) admit.
+ admit.
+ inline Mp(Syscall).__expand_seed_ Mp(Syscall)._expand_seed. wp ; sp. call expand_seed_correct. by rewrite len_val /XMSS_WOTS_LEN. skip => />. progress.
    + admit.
    + smt().
    + smt().
    + smt().
qed.
