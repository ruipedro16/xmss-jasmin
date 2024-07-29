
pragma Goals : printall.

require import AllCore List RealExp IntDiv.
from Jasmin require import JModel JArray.

require import Params Parameters Address Notation Hash Primitives Wots Generic Util.
require import RandomBytes XMSS_IMPL.

require import Array2 Array3 Array8 Array32 Array64 Array67 Array96 Array128 Array2144.

require import Utils. (* valid ptr predicate & W64ToBytes & addr_to_bytes *)
require import Correctness_Mem. (* memcpy results *)
(*---*) import NBytes.
require import Termination.
require import Repr.

require import BitEncoding.
(*---*) import BitChunking.

op thash_f_padding_val : W64.t.

module Hop2 = {
  proc thash_f (out : nbytes, seed : nbytes, address : adrs) : nbytes * adrs = {
    var padding : W8.t list;
    var addr_bytes : W8.t list;
    var u : nbytes;
    var bitmask : nbytes;
    var buf : W8.t list;
    var i : int;
    var t : W8.t;
    
    padding <@ Util.w64_to_bytes (thash_f_padding_val, padding_len);
    addr_bytes <- addr_to_bytes address;
    u <@ Hash.prf (addr_bytes, seed);

    address <- set_key_and_mask address 1;
    addr_bytes <- addr_to_bytes address;
    
    bitmask <@ Hash.prf (addr_bytes, seed);

    buf <- padding ++ u;

    i <- 0;
    while (i < n) {
      t <- nth witness out i;
      t <- (t `^` (nth witness bitmask i));
      buf <- put buf ((32 + 32) + i) t;
      i <- i + 1;
    }

    out <- Hash buf;

    return (out, address);
  } 

  proc chain(X : nbytes, start steps : int, _seed : seed, address : adrs) : nbytes * adrs = {
    var t : nbytes <- X;
    var addr_bytes : W8.t list;
    var i : int;

    i <- start;

    while (i < start + steps) {
      address <- set_hash_addr address i;
      address <- set_key_and_mask address 0;

      (t, address) <@ thash_f (t, _seed, address);
      
      i <- i + 1;
    }
    
    return (t, address);
   }

   proc pseudorandom_genSK(sk_seed : nbytes, seed : nbytes, address : adrs) : wots_sk * adrs= {
       var sk : wots_sk <- nseq len (nseq n witness);
       var sk_i : nbytes;
       var i : int;
       var addr_bytes : W8.t list;
    
       address <- set_hash_addr address 0;
       address <- set_key_and_mask address 0;

       i <- 0;
       while (i < len) {
       address <- set_chain_addr address i;
       addr_bytes <- addr_to_bytes address;
       sk_i <@ Hash.prf_keygen ((seed ++ addr_bytes), sk_seed);
       sk <- put sk i sk_i;
       i <- i + 1;
     }

       return (sk, address);
  }

  proc sign (M : wots_message, sk : wots_sk, _seed : seed, address : adrs) : wots_signature * adrs = {
      var sig : wots_signature <- witness;

      return (sig, address);
  }

}.

(*** ***)







(** ----------------------------------------------------------------------------------- **)
lemma base_w_correctness_67 ( _in_ : W8.t Array32.t) :
    floor (log2 w%r) = XMSS_WOTS_LOG_W /\ 
    w = XMSS_WOTS_W => 
      equiv[M(Syscall).__base_w_67_32 ~ BaseW.base_w :
        arg{1}.`2 = _in_ /\
        arg{2} = (to_list _in_, 67) ==>
         res{2} = map (W32.to_uint) (to_list res{1})].
proof.
admit.
qed.
(** ----------------------------------------------------------------------------------- **)

lemma sign_correct (_msg_ _seed_ _pub_seed_ : W8.t Array32.t, _addr_ : W32.t Array8.t) :
    n = XMSS_N /\
    len = XMSS_WOTS_LEN /\
    floor (log2 w%r) = XMSS_WOTS_LOG_W /\ 
    w = XMSS_WOTS_W => 
    equiv [
      M(Syscall).__wots_sign ~ WOTS.sign_seed : 
      arg{1}.`2 = _msg_ /\
      arg{1}.`3 = _seed_ /\
      arg{1}.`4 = _pub_seed_ /\
      arg{1}.`5 = _addr_ /\
      arg{2} = (to_list _msg_, to_list _seed_, to_list _pub_seed_, _addr_)
      ==>
      res{1}.`1 = DecodeWotsSignature res{2}.`1 /\ res{1}.`2 = res{2}.`2
    ].
proof.
move => [#] ????.
proc => //=.
seq 1 1 : (#pre /\ size (flatten sig{2}) = 2144); first by auto => />; smt(@List).
swap {1} 1 1.
seq 1 1 : (
  #pre /\ forall (k : int), 0 <= k < 2144 => sig{1}.[k] = nth witness (flatten wots_skey{2}) k
).
    + inline {1} M(Syscall).__expand_seed_ M(Syscall)._expand_seed; wp; sp.
      admit. (* call lemma equiv expand seed pseudorandom gensk *)
inline {1} M(Syscall).__chain_lengths_ M(Syscall)._chain_lengths M(Syscall).__chain_lengths.
seq 9 0 : (#pre /\ msg2{1} = _msg_); 1:auto.
seq 1 1 : (
    #pre /\ 
    msg{2} = map (W32.to_uint) (to_list lengths2{1})
).
    + admit. (* ecall {1} (base_w_correctness_67 msg2{1}). : Invalid goal shape *)
seq 7 7 : (#pre); 1:admit.
while (
  len{2} = 67 /\ 
  ={i} /\
  address{2} = addr{1} /\
  sig{1} = DecodeWotsSignature sig{2}
); last first.
    + auto => /> &1 &2 *. split; last by smt(). rewrite /DecodeWotsSignature. admit.
seq 2 2 : (#pre); first by inline; auto.
seq 3 3 : (#post); last by auto => /> /#. 
admit.
qed.





















lemma thash_f_hop2_correct (o : W8.t Array32.t, ps : W8.t Array32.t, a : W32.t Array8.t) :
    n = XMSS_N /\
    padding_len = XMSS_PADDING_LEN /\ 
    prf_padding_val = XMSS_HASH_PADDING_F =>
    equiv [
      M(Syscall).__thash_f ~ Hop2.thash_f :
      arg{1} = (o, ps, a) /\
      arg{2} = (to_list o, to_list ps, a)
      ==>
      res{2}.`1 = to_list res{1}.`1 /\
      res{2}.`2 = res{1}.`2
      ].
proof.
(*
rewrite /XMSS_N /XMSS_PADDING_LEN /XMSS_HASH_PADDING_F => [#] nval plen pval.
proc => //=.
seq 15 9 : (buf{2} = to_list buf{1} /\ address{2} = addr{1}); last first.
 + inline M(Syscall).__core_hash__96 M(Syscall)._core_hash_96; wp; sp; ecall {1} (hash_96 in_00{1}); auto => /> /#.
seq 4 0 : (#pre); 1:auto.
swap {2} 1 1.
seq 1 1 : (#pre /\ addr_bytes{2} = to_list addr_as_bytes{1}).
  + ecall {1} (addr_to_bytes_correct addr{1}); auto => /> /#. 
seq 1 0 : (#pre); 1:auto.
seq 1 1 : (#pre /\ to_list padding{1} = padding{2}).
  + call (ull_to_bytes_correct W64.zero); auto => />.  
seq 1 0 : (
  #pre /\
  forall (k : int), 0 <= k < 32 => buf{1}.[k] = padding{1}.[k]
); first by auto => />; smt(@Array96).
seq 1 1 : (
  out{2} = to_list out{1} /\
  seed{2} = to_list pub_seed{1} /\
  address{2} = addr{1} /\

  addr_bytes{2} = to_list addr_as_bytes{1} /\
  padding{2} = to_list padding{1} /\
  (forall (k : int), 0 <= k && k < 32 => buf{1}.[k] = padding{1}.[k]) /\

  u{2} = to_list aux{1}
).
    + exists * addr_as_bytes{1}, pub_seed{1}; elim * => _P1 _P2. call {1} (prf__hop2 _P1 _P2); [admit | auto => /> ]. (* o primeiro admit e pq na spec nao ha distincao entre padding para prf e para prf kg => TODO: Mudar isto *)
seq 1 0 : (
    #pre /\
    forall (k : int), 32 <= k < 64 => buf{1}.[k] = aux{1}.[k - 32]
); first by auto => /> &1 *; smt(@Array96). 
seq 1 1 : (#pre); first by inline {1} ; auto.
seq 1 1 : (#pre); first by ecall {1} (addr_to_bytes_correctness addr{1}); auto => /> /#.
seq 1 1 : (#pre /\ bitmask{2} = to_list bitmask{1}).
    + exists * addr_as_bytes{1}, pub_seed{1}; elim * => _P1 _P2. call {1} (prf__hop2 _P1 _P2); [admit | auto => /> ]. (* o primeiro admit e pq na spec nao ha distincao entre padding para prf e para prf kg => TODO: Mudar isto *)
seq 0 1 : (
  #pre /\
  forall (k : int), 0 <= k < 64 => buf{1}.[k] = nth witness buf{2} k
); first by auto => /> &1 *; rewrite !/to_list !/mkseq -!iotaredE => /> /#.
while (
  #pre /\
  0 <= to_uint i{1} <= 32 /\
  i{2} = to_uint i{1} /\
  forall (k : int), 0 <= k < i{2} => buf{1}.[64 + k] = nth witness buf{2} (64 + k)
).
    + auto => /> &1 &2 *. do split; 4..6,8,9:smt(@W64 pow2_64).
      * admit.
      * admit.
      * admit.
      * admit.
    + auto => /> &1 &2 *. do split; 1,2:smt(). move => *. admit.
*)
admit.
qed.


lemma gen_chain_hop2 (_in : W8.t Array32.t, _start_ _steps_ : W32.t, 
                         _pub_seed_ : W8.t Array32.t, _addr_ : W32.t Array8.t) :
    n = XMSS_N /\
    padding_len = XMSS_PADDING_LEN /\ 
    prf_padding_val = XMSS_HASH_PADDING_F =>
    equiv [
      M(Syscall).__gen_chain_inplace ~ Hop2.chain : 
      arg{1} = (_in, _start_, _steps_, _pub_seed_, _addr_) /\
      arg{2} = (to_list _in, to_uint _start_, to_uint _steps_, to_list _pub_seed_, _addr_) /\
      0 <= to_uint _start_ <= 15 /\
      0 <= to_uint _steps_ <= 15 /\
      0 <= to_uint (_start_ + _steps_) <= 15
      ==> 
      res{2}.`1 = to_list res{1}.`1 /\ 
      res{2}.`2 = res{1}.`2
    ].
proof.
move => [#] ???.
proc => //=.
seq 3 2 : (
  #pre /\ 
  i{1} = start{1} /\ 
  t{1} = start{1} + steps{1} /\ 
  t{2} = X{2} /\
  i{2} = start{2} /\
  i{2} = to_uint i{1}
); 1:auto.
while (
    0 <= to_uint start{1} <= 15 /\
    0 <= to_uint steps{1} <= 15 /\
    0 <= to_uint (start{1} + steps{1}) <= 15 /\
  
    t{1} = start{1} + steps{1} /\
  
    0 <= to_uint i{1} <= 15 /\
    _seed{2} = to_list pub_seed{1} /\
    address{2} = addr{1} /\
    t{2} = to_list out{1} /\
    i{2} = to_uint i{1} /\
    start{2} = to_uint start{1} /\
    steps{2} = to_uint steps{1}
); last first.
    + auto => /> *; smt(@W32 pow2_32). 
    + seq 2 2 : (#pre); first by inline {1}; auto => />. 
      inline M(Syscall).__thash_f_ M(Syscall)._thash_f; wp; sp.
      exists * out1{1}, pub_seed1{1}, addr1{1}; elim * => _P1 _P2 _P3; call {1} (thash_f_hop2_correct _P1 _P2 _P3). 
      auto => /> &1 &2 *; smt(@W32 pow2_32).
qed.

lemma chain_hop2_spec : equiv [ Hop2.chain ~ Chain.chain : ={arg} ==> ={res} ].
proof.
proc => //=.
while (
  #pre /\
  ={address, t} /\
  i{1} = i{2} + chain_count{2}
); last by auto => /> /#. 
    + seq 2 2 : (#pre); first by auto.
      inline Hop2.thash_f. sp 3 0.
admit.
qed.


lemma chain_correct (_in : W8.t Array32.t, _start_ _steps_ : W32.t, 
                         _pub_seed_ : W8.t Array32.t, _addr_ : W32.t Array8.t) :
    equiv [
      M(Syscall).__gen_chain_inplace ~ Chain.chain : 
      arg{1} = (_in, _start_, _steps_, _pub_seed_, _addr_) /\
      arg{2} = (to_list _in, to_uint _start_, to_uint _steps_, to_list _pub_seed_, _addr_) /\
      0 <= to_uint _start_ <= 15 /\
      0 <= to_uint _steps_ <= 15 /\
      0 <= to_uint (_start_ + _steps_) <= 15
      ==> 
      res{2}.`1 = to_list res{1}.`1 /\ 
      res{2}.`2 = res{1}.`2
    ].
proof.
(* transitivity . *)
admit.
qed.




(*------------------------------------------------------------------------------------------------------------------------------------------------------*)




op load_wots_signature (mem : global_mem_t) (ptr : W64.t) : W8.t list = mkseq (fun (i : int) => loadW8 mem (to_uint ptr + i)) 2144.

(*
lemma pk_from_sig_hop2  (mem : global_mem_t) (_sig_ptr_ : W64.t, _msg_ : W8.t Array32.t, 
                                              _pub_seed_ : W8.t Array32.t, _addr_ : W32.t Array8.t):
    equiv[ M(Syscall).__wots_pk_from_sig ~ WOTS.pkFromSig :
      arg{1} = (_pk_, _sig_ptr_, _msg_, _pub_seed_, _addr_) /\
      arg{2} = (to_list _msg_, load_wots_signature mem _sig_ptr_, to_list _pub_seed_, _addr_)
      ==>
      true
    ].

*)


















(*** ***)

op encode_wots_sk (sk_spec : wots_sk) : W8.t Array2144.t =
    Array2144.of_list witness (flatten sk_spec).

lemma expand_seed_correct (
    _in_seed : W8.t Array32.t, _pub_seed : W8.t Array32.t, _addr : W32.t Array8.t):
    len = XMSS_WOTS_LEN /\ n = XMSS_N =>
    equiv [M(Syscall).__expand_seed ~ Hop2.pseudorandom_genSK :
      arg{1}.`2 = _in_seed /\ 
      arg{1}.`3 = _pub_seed /\
      arg{1}.`4 = _addr /\
      arg{2} = (to_list _in_seed, to_list _pub_seed, _addr) ==>
      res{1}.`1 = encode_wots_sk res{2}.`1 /\ 
      res{1}.`2 = res{2}.`2].
proof.
rewrite /XMSS_WOTS_LEN /XMSS_N; move => [len_val n_val].
proc; auto => />.
conseq (: _ ==>  addr{1} = address{2} /\ forall (k : int), 0 <= k < 2144 => outseeds{1}.[k] = nth witness (flatten sk{2}) k).
  + auto => /> rL rR. rewrite /encode_wots_sk. rewrite /of_list. auto => />. admit.
seq 3 1 : (
  #pre /\
  buf{1} = witness /\
  ith_seed{1} = witness /\
  addr_bytes{1} = witness /\
  size sk{2} = len /\
  size (flatten sk{2}) = 2144
).
    + auto => />. split; smt(@List).
seq 2 2 : ( (* Same as # pre but without addr{1/2} = _addr *)
  inseed{1} = _in_seed /\
  pub_seed{1} = _pub_seed /\
  sk_seed{2} = to_list _in_seed /\
  seed{2} = to_list _pub_seed /\
  ith_seed{1} = witness /\ 
  size sk{2} = len /\ 
  size (flatten sk{2}) = 2144 /\
  addr{1} = address{2}
); first by inline {1}; auto => />.
seq 1 0 : (#pre /\ aux{1} = pub_seed{1}); first by ecall {1} (_x_memcpy_u8u8_post pub_seed{1}); auto => />.
seq 1 0 : (#pre /\ (forall (k : int), 0 <= k < 32 => buf{1}.[k] = pub_seed{1}.[k])); first by auto => /> *; smt(@Array64).
while (
  (* This is from pre *)
  size sk{2} = len /\ size (flatten sk{2}) = 2144 /\
  
  0 <= i{1} <= 67 /\ ={i} /\

  addr{1} = address{2} /\
  addr_bytes{2} = to_list addr_bytes{1} /\
  sk_i{2} = to_list ith_seed{1} /\
  buf{1} = Array64.of_list witness (seed{2} ++ addr_bytes{2}) /\
  
  forall (k : int), 0 <= k < 32 * i{2} => outseeds{1}.[k] = nth witness (flatten sk{2}) k
); last first.
+ auto => /> &1 &2 *. do split.
    - admit.
    - admit.
    - admit.
    - smt(@List @Array2144).
    - by rewrite len_val.
    - move => *. admit.
seq 1 1 : (#pre); first by inline {1}; auto => />.
auto => />.
    + move => &1 &2. move => [#] ?????????????????. move => [#] ?????????????. do split.
        * smt().
        * smt().
        * smt().
        * smt().
        * smt().
        * smt().
        * smt().
        * smt().
        * smt().
        * auto => /> k *. rewrite initE. case (0 <= k && k < 2144); last by smt(). move => ?. 
          case (i{1} * 32 <= k && k < i{1} * 32 + 32); 1,2:by move => ?; smt(@List @Array2144). 
        * smt().
        * smt().
auto => />.
(*
seq 1 0 : (#pre). auto => /> &1 &2 *. apply (eq_from_nth witness). by rewrite !size_to_list. admit.
seq 1 1 : (#pre).
    + ecall {1} (addr_to_bytes_correctness addr{1}). auto => /> &1 &2 *. admit.
*)
admit.
qed.
