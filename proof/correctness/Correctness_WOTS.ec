pragma Goals : printall.

require import AllCore List RealExp IntDiv.
from Jasmin require import JModel JArray.

require import Params Parameters Address Notation Primitives Wots Generic.
require import XMSS_IMPL XMSS_IMPL_PP.

require import Array3 Array8 Array32 Array67 Array2144.

require import Utils. (* valid ptr predicate *)
require import Correctness_Hash.

  lemma base_w_correctness_67 (_out : W32.t Array67.t, _in_ : W8.t Array32.t) :
      floor (log2 w%r) = XMSS_WOTS_LOG_W /\ 
      w = XMSS_WOTS_W => 
      equiv[M(Syscall).__base_w_67_32 ~ BaseW.base_w :
        arg{1} = (_out, _in_) /\
        arg{2} = (to_list _in_, 67) ==>
          res{2} = mkseq (fun i => to_uint res{1}.[i]) 67].
  proof.
  rewrite /XMSS_WOTS_LOG_W /XMSS_WOTS_W ; move => [logw_val w_val].
  proc.
while (
  outlen{2} = 67 /\
  _in{2} = to_uint in_0{1} /\ 
  0 <= to_uint in_0{1} <= 34 /\
  to_uint total{1} = to_uint total{2} /\ 
  0 <= to_uint total{1} <= W8.max_uint /\
  bits{2} = to_uint bits{1} /\  
  0 <= to_uint bits{1} <= 4 /\
  consumed{2} = to_uint i{1} /\
  0 <= to_uint i{1} <= 67 /\
  X{2} = to_list input{1} /\
  (forall (k : int), 0 <= k < to_uint i{1} => nth witness base_w{2} k = to_uint output{1}.[k])
) ; auto => /> ; last first.
- move => &2 * ; split.
    + smt(). 
    + move => ???????????????? H0 H1 H2. admit. (* FIXME: use H0 H1 & H2 to prove this *)
- progress. 
    + rewrite to_uintD /#.
    + rewrite to_uintD /#.
    + admit.
    + admit.
    + admit.
    + admit.
    + by rewrite logw_val.
    + rewrite to_uintD /#.
    + rewrite to_uintD /#.
    + admit.
    + rewrite logw_val w_val /=. admit.
    + smt(@W64).
    + rewrite ultE to_uintD /#.
    + admit.
    + admit.
    + admit.
    + admit.
    + rewrite logw_val to_uintD to_uintN /=. admit.
    + rewrite to_uintD /#.
    + smt(@W64).
    + rewrite to_uintD /#.
    + rewrite to_uintD /#.
    + smt(@W64).
    + admit.
    + smt(@W64).
    + rewrite ultE to_uintD /#.
    + admit.
    + admit.
    + admit.
    + rewrite logw_val. admit. 
    + rewrite to_uintD /#.
    + admit.
    + rewrite to_uintD /#.
    + rewrite to_uintD /#.
    + smt(@W64).
    + admit.
    + smt(@W64).
    + rewrite ultE to_uintD /#.
qed.

lemma wots_checksum_correctness (msg : W32.t Array67.t) :
    len1 = XMSS_WOTS_LEN1 /\  w = XMSS_WOTS_W =>
    equiv [Mp(Syscall).__csum ~ WOTS.checksum :
      (forall (k : int), 0 <= k < 67 => 0 <= to_uint msg.[k] <= (w - 1)) /\
      arg{1} = msg /\ arg{2} = mkseq (fun i => to_uint msg.[i]) 67  ==> to_uint res{1} = res{2}].
proof.
rewrite /XMSS_WOTS_LEN1 /XMSS_WOTS_W ; move => [len1_val w_val].
proc => /=.
while (
  #pre /\
  to_uint csum{1} = checksum{2} /\
  i{2} = to_uint i{1} /\   m{2} = mkseq (fun i => to_uint msg_base_w{1}.[i]) 67 /\
  0 <= i{2} <= len1
); last by auto => /> * ; rewrite len1_val.
auto => />  &1 &2 * ; do split.
    + rewrite w_val /=.
      have E: nth witness (mkseq (fun (i0 : int) => to_uint msg.[i0]) 67) (to_uint i{1}) = to_uint (JWord.W2u32.zeroextu64 msg.[to_uint i{1}]) by rewrite nth_mkseq ; smt. (* NOTE: TODO: FIXME:  smt(@JWord) should work but doesnt *)
      rewrite E to_uintD of_uintK. admit. (* From the spec we know that len1 * (w - 1) * 2^8 *)
    + rewrite to_uintD /#.
    + smt().
    + rewrite len1_val /#.
    + rewrite ultE of_uintK to_uintD /#.
    + rewrite len1_val ultE of_uintK to_uintD /#.
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
