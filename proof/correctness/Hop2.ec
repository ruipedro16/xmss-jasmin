
pragma Goals : printall.

require import AllCore List RealExp IntDiv.
from Jasmin require import JModel JArray.

require import Params Parameters Address Notation Hash Primitives Wots Util.
require import XMSS_IMPL.

require import Array2 Array3 Array8 Array32 Array64 Array67 Array96 Array128 Array2144.

require import Utils. (* valid ptr predicate & W64ToBytes & addr_to_bytes *)
require import Correctness_Mem Correctness_Hash. (* memcpy results *)
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

    buf <- nseq 96 witness;
    
    padding <@ Util.w64_to_bytes (thash_f_padding_val, padding_len);
    addr_bytes <- addr_to_bytes address;
    u <@ Hash.prf (addr_bytes, seed);

    address <- set_key_and_mask address 1;
    addr_bytes <- addr_to_bytes address;
    
    bitmask <@ Hash.prf (addr_bytes, seed);

    (* buf <- padding ++ u; *)
    buf <- mkseq (fun (i : int) => if (0 <= i < 32) then nth witness padding i else nth witness buf i) 96;
    buf <- mkseq (fun (i : int) => if (32 <= i < 64) then nth witness u (i - 32) else nth witness buf i) 96;

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
(* This is proved in WOTS *)
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

lemma base_w_correctness_3 ( _in_ : W8.t Array2.t) :
    floor (log2 w%r) = XMSS_WOTS_LOG_W /\ 
    w = XMSS_WOTS_W => 
      equiv [M(Syscall).__base_w_3_2 ~ BaseW.base_w :
        arg{1}.`2 = _in_ /\
        arg{2} = (to_list _in_, 3) ==>
         res{2} = map (W32.to_uint) (to_list res{1})].
proof.
admit.
qed.


lemma wots_checksum_correctness (msg : W32.t Array67.t) :
    len1 = XMSS_WOTS_LEN1 /\  w = XMSS_WOTS_W =>
    equiv [M(Syscall).__csum ~ WOTS.checksum :
      (forall (k : int), 0 <= k < 67 => 0 <= to_uint msg.[k] <= 15) /\ (* 15 = w - 1 *)
      arg{1} = msg /\ arg{2} = map (W32.to_uint) (to_list msg) ==>
        to_uint res{1} = res{2}].
proof.
admit.
qed.

(** ----------------------------------------------------------------------------------- **)

lemma sign_seed_correct (_msg_ _seed_ _pub_seed_ : W8.t Array32.t, _addr_ : W32.t Array8.t) :
    n = XMSS_N /\
    len = XMSS_WOTS_LEN /\
    floor (log2 w%r) = XMSS_WOTS_LOG_W /\ 
    w = XMSS_WOTS_W /\
    len1 = XMSS_WOTS_LEN1 /\
    len2 = XMSS_WOTS_LEN2 => 
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
rewrite /XMSS_WOTS_W /XMSS_WOTS_LEN1 /XMSS_WOTS_LEN2 => [#] ??? w_val len1_val len2_val.
proc => //=.
conseq (: _ ==> addr{1} = address{2} /\ (forall (k : int), 0 <= k < 2144 => sig{1}.[k] = nth witness (flatten sig{2}) k)).
  + auto => /> *; rewrite /DecodeWotsSignature /of_list /mkseq tP => ??; smt(@Array2144 @List).
seq 1 0 : (
  M{2} = to_list msg{1} /\
  sk_seed{2} = to_list seed{1} /\
  pub_seed{2} = to_list pub_seed{1} /\
  address{2} = addr{1}
); first by auto.
seq 0 1 : (#pre /\ size sig{2} = len /\ size (flatten sig{2}) = len * n).
  + auto => />; smt(@List).
swap {1} 1 1.
seq 1 1 : (#pre /\ wots_skey{2} = EncodeWotsSk sig{1}).
  + inline {1} M(Syscall).__expand_seed_ M(Syscall)._expand_seed; wp; sp.
    exists * inseed0{1}, pub_seed{1}, addr1{1}; elim * => _P1 _P2 _P3; call {1} (expand_seed_correct _P1 _P2 _P3); skip => />.
inline {1} M(Syscall).__chain_lengths_ M(Syscall)._chain_lengths M(Syscall).__chain_lengths.
sp 9 0.
seq 1 1 : (
  M{2} = to_list msg{1} /\
  sk_seed{2} = to_list seed{1} /\
  pub_seed{2} = to_list pub_seed{1} /\ 
  address{2} = addr{1} /\
  size sig{2} = len /\ 
  size (flatten sig{2}) = len * n /\
  wots_skey{2} = EncodeWotsSk sig{1} /\
  msg{2} = map (W32.to_uint) (to_list lengths2{1}) /\
  (forall (k : int), 0 <= k < 67 => 0 <= nth witness msg{2} k <= 15) (* 15 = w - 1 *)    
).
    + exists * msg2{1}; elim * => _P1; call {1} (base_w_correctness_67 _P1); first by smt(). skip => /> *. split. admit. (* TODO: isto e falso. nao perceboo de onde vem ete subgoal *)
      admit. (* TODO: preciso de provar que a pos condicao de base w e forall k in res, 0 <= res.[k] <= 15 *)
inline {1} M(Syscall).__wots_checksum.
seq 6 1 : (#pre /\ csum{2} = to_uint csum{1}).
    + sp; exists * msg_base_w{1}; elim * => _P1; call {1} (wots_checksum_correctness _P1); first by smt(). skip => /> *. admit. 
seq 4 2 : (
  M{2} = to_list msg{1} /\
  sk_seed{2} = to_list seed{1} /\
  pub_seed{2} = to_list pub_seed{1} /\ 
  address{2} = addr{1} /\
  size sig{2} = len /\ 
  size (flatten sig{2}) = len * n /\
  wots_skey{2} = EncodeWotsSk sig{1} /\
  msg{2} = map (W32.to_uint) (to_list lengths2{1}) /\
  (forall (k : int), 0 <= k < 67 => 0 <= nth witness msg{2} k <= 15) /\
  to_uint csum_32{2} = to_uint csum{1}
).
    + auto => /> *. admit.
seq 0 1 : (#pre /\ len_2_bytes{2} = 3). 
    + auto => /> *. rewrite w_val len2_val. admit. (* This is false => rever a spec*)
seq 2 1 : (#pre /\ csum_bytes{2} = to_list csum_bytes_p{1}).
    + admit. (* This needs to be refactored in the spec *)
seq 1 1 : (#pre /\ csum_base_w{2} = map (W32.to_uint) (to_list csum_base_w{1})).
    + exists * csum_bytes_p{1}; elim * => _P1. call {1} (base_w_correctness_3 _P1); [ smt() | skip => /> ].
admit.
qed.

(*------------------------------------------------------------------------------------------------------------------------------------------------------*)
