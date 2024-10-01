pragma Goals : printall.

require import AllCore List RealExp IntDiv Distr DList IntDiv.
from Jasmin require import JModel JArray.

require import Params Types Address Hash XMSS_MT_Params XMSS_MT_TreeHash XMSS_MT_Types XMSS_MT_PRF.
require import XMSS_IMPL Parameters.

require import Repr2 Utils2.

require import Array4 Array8 Array32 Array64 Array68 Array96 Array132 Array136 Array352 Array2144.
require import WArray32 WArray96 WArray136.

require import Correctness_Address Correctness_Mem Correctness_Hash.
require import DistrUtils.

require import BitEncoding.
(*---*) import BitChunking.

require import StdBigop. 
(*---*) import Bigint.

require import Termination.

lemma load_store_W64 (mem : global_mem_t) (a : address) (v : W64.t) :
    loadW64 (storeW64 mem a v) a = v.
proof.
rewrite /loadW64 /storeW64 wordP => j?.
rewrite pack8E /stores initiE // => />. 
rewrite initiE 1:/# => />. 
rewrite get_setE.
  + case (a + j %/ 8 = a + 7) => *; [rewrite /(\bits8) initiE /# |].
rewrite get_setE.
  + case (a + j %/ 8 = a + 6) => *; [rewrite /(\bits8) initiE /# |].
rewrite get_setE.
  + case (a + j %/ 8 = a + 5) => *; [rewrite /(\bits8) initiE /# |].
rewrite get_setE.
  + case (a + j %/ 8 = a + 4) => *; [rewrite /(\bits8) initiE /# |].
rewrite get_setE.
  + case (a + j %/ 8 = a + 3) => *; [rewrite /(\bits8) initiE /# |].
rewrite get_setE.
  + case (a + j %/ 8 = a + 2) => *; [rewrite /(\bits8) initiE /# |].
rewrite get_setE.
  + case (a + j %/ 8 = a + 1) => *; [rewrite /(\bits8) initiE /# |].
rewrite get_setE.
  + rewrite ifT 1:/# /(\bits8) initiE /#.
qed.

lemma set_result_post (eq : W8.t) :
    hoare[
      M(Syscall).__set_result :
      arg.`1 = eq
      ==>
      (eq = W8.zero) => res = W64.zero /\
      (eq <> W8.zero) => res = W64.of_int (-1)
    ].
proof.
proc.
auto => />.
case (eq = W8.zero). 
  + rcondf 1; first by skip => [#] ?? => /#.
    call (: true ==> true); last by auto.
    proc; inline; wp; sp; while (true); auto => />. 
  + rcondt 1; first by skip => [#] ?? => /#. 
    auto => />. 
qed.


lemma p_set_result_post (eq : W8.t) :
    phoare[
      M(Syscall).__set_result :
      arg.`1 = eq
      ==>
      (eq = W8.zero) => res = W64.zero /\
      (eq <> W8.zero) => res = W64.of_int (-1)
    ] = 1%r.
proof.
conseq set_result_ll (set_result_post eq).
  + admit. (* Need to add stuff to #pre *)
  + admit.
qed.

(*

arg{1}

m_ptr : W64.t         => ptr to the message 
mlen_ptr : W64.t      => ptr to the message length 
sm_ptr : W64.t        => ptr to the signed message
smlen : W64.t         => length of the signed message = mlen + sig bytes
pk : W8.t Array64.t   => public key

arg{2}

pk : xmss_pk  => public key 
m : msg_t     => message 
s : sig_t    => signature How to encode signature ?
*)

(* Load the signed message from memory. res = m || sig *)
op load_sm_mem (mem : global_mem_t) (ptr sm_len : W64.t) : W8.t list =
    mkseq (fun (i : int) => loadW8 mem (to_uint ptr + i)) (to_uint sm_len).

(* Load the signature from memory. Skips the message *)
op load_sig_mem (mem : global_mem_t) (sm_ptr sm_len : W64.t) : W8.t list =
    let mlen : int = to_uint sm_len - XMSS_SIG_BYTES in
    mkseq (fun (i : int) => loadW8 mem (to_uint sm_ptr + mlen + i)) XMSS_SIG_BYTES.

print EncodeSignature. (* byte list -> sig_t *)
print load_signature_mem. (* ptr & len  -> byte list *)

lemma verify_correctness (mem : global_mem_t)  (ptr_m ptr_mlen ptr_sm sm_len : W64.t) (_pk : W8.t Array64.t) :
    n = XMSS_N /\
    d = XMSS_D /\
    h = XMSS_FULL_HEIGHT =>
    equiv [
      M(Syscall).__xmssmt_core_sign_open ~ XMSS_MT_PRF.verify :
      
      Glob.mem{1} = mem /\

      0 < to_uint (loadW64 mem (to_uint ptr_mlen)) < W64.max_uint /\
      valid_ptr_i ptr_sm (4 + 32) /\

      arg{1} = (ptr_m, ptr_mlen, ptr_sm, sm_len, _pk) /\
      arg{2}.`1 = EncodePkNoOID _pk /\
      arg{2}.`2 = load_sig_mem mem ptr_sm sm_len /\
      arg{2}.`3 = EncodeSignature ( load_signature_mem mem ptr_sm (sm_len - W64.of_int XMSS_SIG_BYTES) )
      ==>
      res{2}  <=> res{1} = W64.zero /\
      (!res{2} <=> res{1} = W64.of_int (-1))
    ].
proof.
rewrite /XMSS_N /XMSS_D /XMSS_FULL_HEIGHT => [#] n_val d_val h_val.
proc => /=. 
seq 9 0 : #pre; first by auto.
seq 29 17 : (is_valid{2} <=> are_equal{1} = W8.zero); last first.
  + ecall {1} (p_set_result_post are_equal{1}).
    auto => /> &1 r *.
    case (are_equal{1} = W8.zero) => *.
       - admit.
       - admit.
        
seq 3 0 : (
  #pre /\
  sm_offset{1} = W64.zero /\
  to_list pub_root{1} = sub pk{1} 0 32 /\
  to_list pub_seed{1} = sub pk{1} 32 32
).
    + auto => /> *; do split.
        * apply (eq_from_nth witness); first by rewrite size_to_list size_sub.
          rewrite size_to_list => j?.
          by rewrite nth_sub // get_to_list initiE. 
        * apply (eq_from_nth witness); first by rewrite size_to_list size_sub.
          rewrite size_to_list => j?.
          by rewrite nth_sub // get_to_list initiE. 
swap {1} 4 -2.
seq 2 0 : (
    #pre /\
    ots_addr{1}.[0] = W32.zero /\
    ots_addr{1}.[1] = W32.zero /\
    ots_addr{1}.[2] = W32.zero /\
    ots_addr{1}.[3] = W32.zero /\
    ots_addr{1}.[4] = W32.zero /\
    ots_addr{1}.[5] = W32.zero /\
    ots_addr{1}.[6] = W32.zero /\
    ots_addr{1}.[7] = W32.zero
).
    + inline M(Syscall).__zero_address_  M(Syscall).__set_type; wp; ecall {1} (zero_addr_res addr{1}).
      auto => />.
seq 4 0 : (
    #pre /\
    
    ltree_addr{1}.[0] = W32.zero /\
    ltree_addr{1}.[1] = W32.zero /\
    ltree_addr{1}.[2] = W32.zero /\
    ltree_addr{1}.[3] = W32.one /\
    ltree_addr{1}.[4] = W32.zero /\
    ltree_addr{1}.[5] = W32.zero /\
    ltree_addr{1}.[6] = W32.zero /\
    ltree_addr{1}.[7] = W32.zero /\
  
    node_addr{1}.[0] = W32.zero /\
    node_addr{1}.[1] = W32.zero /\
    node_addr{1}.[2] = W32.zero /\
    node_addr{1}.[3] = W32.of_int 2 /\
    node_addr{1}.[4] = W32.zero /\
    node_addr{1}.[5] = W32.zero /\
    node_addr{1}.[6] = W32.zero /\
    node_addr{1}.[7] = W32.zero
).
    + inline {1} 3.
      inline {1} 7. 
      inline {1} 2.
      wp.
      ecall {1} (zero_addr_res addr1{1}).
      inline {1} 1.
      wp.
      ecall {1} (zero_addr_res addr2{1}).
      auto => />.
 
(* this conseq simplifies #pre so that it fits on the screen *)
conseq (:
    Glob.mem{1} = mem /\
    (0 < to_uint (loadW64 mem (to_uint ptr_mlen)) < W64.max_uint) /\
    valid_ptr_i ptr_sm 36 /\
    m_ptr{1} = ptr_m /\
    mlen_ptr{1} = ptr_mlen /\
    sm_ptr{1} = ptr_sm /\ 
    smlen{1} = sm_len /\ 
    pk{1} = _pk /\
    pk{2} = EncodePkNoOID _pk /\
    m{2} = load_sig_mem mem ptr_sm sm_len /\ 
    s{2} = EncodeSignature
       (load_signature_mem mem ptr_sm (sm_len - (of_int XMSS_SIG_BYTES)%W64)) /\
    sm_offset{1} = W64.zero /\
    to_list pub_root{1} = sub pk{1} 0 32 /\
    to_list pub_seed{1} = sub pk{1} 32 32 /\

    ots_addr{1} = zero_address /\
    ltree_addr{1} = zero_address.[3 <- W32.one] /\
    node_addr{1} = zero_address.[3 <- W32.of_int 2]

    ==>
    _
).
    + auto => /> &1 &2 *; do split.
         * rewrite /zero_address tP => j?.
           rewrite initiE // /#.
         * rewrite /zero_address tP => j?.
           rewrite get_setE // initiE //.
           case (j = 3) => /#. 
         * rewrite /zero_address tP => j?.
           rewrite get_setE // initiE //.
           case (j = 3) => /#. 

(* This corresponds to *mlen = smlen - params->sig_bytes;
   Not useful for the proof but #pre no longer holds 
*)
seq 3 0 : (
  (0 < to_uint (loadW64 mem (to_uint ptr_mlen))  < W64.max_uint) /\
  valid_ptr_i ptr_sm 36 /\
  m_ptr{1} = ptr_m /\
  mlen_ptr{1} = ptr_mlen /\
  sm_ptr{1} = ptr_sm /\
  smlen{1} = sm_len /\
  pk{1} = _pk /\
  pk{2} = EncodePkNoOID _pk /\
  m{2} = load_sig_mem mem ptr_sm sm_len /\
    s{2} = EncodeSignature
       (load_signature_mem mem ptr_sm (sm_len - (of_int XMSS_SIG_BYTES)%W64)) /\
  sm_offset{1} = W64.zero /\
  to_list pub_root{1} = sub pk{1} 0 32 /\
  to_list pub_seed{1} = sub pk{1} 32 32 /\
  ots_addr{1} = zero_address /\
  ltree_addr{1} = zero_address.[3 <- W32.one] /\
  node_addr{1} = zero_address.[3 <- (of_int 2)%W32]
); first by auto.

seq 1 2 : (
  #pre /\ 
  to_uint idx{1} = to_uint idx_sig{2} /\
  idx_sig{2} = s{2}.`sig_idx
).
    + auto => />.
      admit. 

(* This corresponds to the comment 

    /* Put the message all the way at the end of the m buffer, so that we can
     * prepend the required other inputs for the hash function. */      
    
    This is not useful for the proof 
*)
seq 4 0 : (#pre).
    + seq 3 0 : (#pre /\ 0 <= to_uint bytes{1} < W64.max_uint).
         * auto => /> &1 *; split. 
              - admit.
              - admit. (* A partir de #pre nao sei que Glob.mem.[ptr_m] = mem.[ptr_m] *)

      inline {1}.
      while {1} (#post) (to_uint bytes2{1} - to_uint i0{1}).
         * auto => /> &hr *; smt(@W64 pow2_64).
         * auto => /> &1 *; rewrite ultE /#.
  
seq 0 2 : (
    #pre /\
    val seed{2} = to_list pub_seed{1} /\
    address{2} = zero_address
).
    + auto => /> &1 &2 ???? -> *. 
      (* A seta refere se a hipotese to_list pub_seed{1} = sub _pk 32 32 *)
      apply (eq_from_nth witness); first by rewrite valP n_val size_sub.
      rewrite valP n_val => j?.
      rewrite /EncodePkNoOID => />.
      by rewrite insubdK; [by rewrite /P size_sub // n_val |].

seq 3 0 : (
  #pre /\
  to_list buf{1} = mkseq (fun i => loadW8 Glob.mem{1} (to_uint sm_ptr{1} + 4 + i)) 32
).
    + ecall {1} (p_memcpy_ptr_correct t64{1}).
      auto => /> &1 &2 *; do split. 
         * rewrite to_uintD of_uintK /= /#.
         * move => ?; rewrite to_uintD of_uintK /= /#. 
         * rewrite to_uintD of_uintK /= /#.
         * move => *.
           apply (eq_from_nth witness); first by rewrite size_to_list size_mkseq. 
           rewrite size_to_list => j?.
           rewrite get_to_list initiE // nth_mkseq // => />.
           congr. 
           rewrite to_uintD_small 2:of_uintK // of_uintK /= /#.  

swap {2} 5 -4.
seq 0 1 : (#pre /\ to_list buf{1} = val _R{2}).
    + auto => /> &1 &2 ???????? ->. 
      apply (eq_from_nth witness).
         * by rewrite valP n_val size_mkseq.
      rewrite size_mkseq => j?.
      rewrite /EncodeSignature => />.
      rewrite insubdK; [by rewrite /P size_sub_list // n_val |].
      rewrite /sub_list !nth_mkseq // => />.
      rewrite /load_signature_mem nth_mkseq /XMSS_SIG_BYTES 1:/# => />.
      rewrite to_uintD.
      admit.


seq 3 0  : (
  #pre /\
  to_uint t64{1} = to_uint m_ptr{1} + 2500 - 32 - 3*32 /\
  to_uint bytes{1} = to_uint smlen{1} - XMSS_SIG_BYTES
).
    + auto => /> &1 &2 *; split.
        * rewrite to_uintD of_uintK /=.  admit. (* Add info to precondition *)
        * admit. (* Not enough info => Adicionar aquela parte que passei a frente *)

seq 0 2 : (
  #pre /\
  idx_tree{2} = idx_sig{2} `>>>` 10 /\
  idx_leaf{2} = idx_sig{2} `&` W32.of_int (2^10 - 1)
); first by auto => /> &1 &2 *; rewrite h_val d_val /=.

swap {2} 2 -1.
seq 0 1 : (#pre /\ val root{2} = sub pk{1} 0 32).
    + auto => /> &1 &2 *.
      apply (eq_from_nth witness).
         * by rewrite valP n_val size_sub.
      rewrite valP n_val => j?.
      rewrite /EncodePkNoOID => />.
      by rewrite insubdK // /P size_sub // n_val.

swap {2} 1 4.

seq 1 2 : (#pre /\ to_list root{1} = val _M'{2}).
    + admit.


seq 0 2 : (
  0 < to_uint (loadW64 mem (to_uint ptr_mlen)) < W64.max_uint /\
  valid_ptr_i ptr_sm 36 /\
  m_ptr{1} = ptr_m /\
  mlen_ptr{1} = ptr_mlen /\
  sm_ptr{1} = ptr_sm /\
  smlen{1} = sm_len /\
  pk{1} = _pk /\
  pk{2} = EncodePkNoOID _pk /\
  m{2} = load_sig_mem mem ptr_sm sm_len /\
  s{2} =
    EncodeSignature (load_signature_mem mem ptr_sm  (sm_len - (of_int XMSS_SIG_BYTES)%W64)) /\
  sm_offset{1} = W64.zero /\
  to_list pub_root{1} = sub pk{1} 0 32 /\
  to_list pub_seed{1} = sub pk{1} 32 32 /\
  ots_addr{1} = zero_address /\
  ltree_addr{1} = zero_address.[3 <- W32.one] /\
  node_addr{1} = zero_address.[3 <- (of_int 2)%W32] /\
  to_uint idx{1} = to_uint idx_sig{2} /\ idx_sig{2} = s{2}.`sig_idx /\
  val seed{2} = to_list pub_seed{1}  /\
  to_list buf{1} =
    mkseq (fun (i0 : int) => loadW8 Glob.mem{1} (to_uint sm_ptr{1} + 4 + i0)) 32 /\
  to_list buf{1} = val _R{2} /\
  to_uint bytes{1} = to_uint smlen{1} - XMSS_SIG_BYTES /\
  idx_tree{2} = idx_sig{2} `>>>` 10 /\
  idx_leaf{2} = idx_sig{2} `&` (of_int (2 ^ 10 - 1))%W32 /\
  val root{2} = sub pk{1} 0 32 /\
  to_list root{1} = val _M'{2} /\
  
  
  address{2} = zero_address.[1 <- idx_tree{2}]
).
    + auto => /> &1 &2 *.
      rewrite /set_tree_addr /set_layer_addr.
      rewrite tP => j?.
      case (j = 0) => *. 
         * by rewrite get_setE // ifF 1:/# get_setE // ifF 1:/# get_setE // ifT // get_setE // ifF 1:/# zero_addr_i.
      case (j = 1) => *.
         * rewrite get_setE // ifF 1:/# get_setE // ifT // get_setE // ifT //.
           admit.
     admit.


seq 2 0 : (
  0 < to_uint (loadW64 mem (to_uint ptr_mlen)) < W64.max_uint /\
  valid_ptr_i ptr_sm 36 /\
  m_ptr{1} = ptr_m /\
  mlen_ptr{1} = ptr_mlen /\
  sm_ptr{1} = ptr_sm /\
  smlen{1} = sm_len /\
  pk{1} = _pk /\
  pk{2} = EncodePkNoOID _pk /\
  m{2} = load_sig_mem mem ptr_sm sm_len /\
  s{2} =
    EncodeSignature (load_signature_mem mem ptr_sm  (sm_len - (of_int XMSS_SIG_BYTES)%W64)) /\
  to_list pub_root{1} = sub pk{1} 0 32 /\
  to_list pub_seed{1} = sub pk{1} 32 32 /\
  ots_addr{1} = zero_address /\
  ltree_addr{1} = zero_address.[3 <- W32.one] /\
  node_addr{1} = zero_address.[3 <- (of_int 2)%W32] /\
  to_uint idx{1} = to_uint idx_sig{2} /\ idx_sig{2} = s{2}.`sig_idx /\
  val seed{2} = to_list pub_seed{1}  /\
  to_list buf{1} =
    mkseq (fun (i0 : int) => loadW8 Glob.mem{1} (to_uint sm_ptr{1} + 4 + i0)) 32 /\
  to_list buf{1} = val _R{2} /\
  to_uint bytes{1} = to_uint smlen{1} - XMSS_SIG_BYTES /\
  idx_tree{2} = idx_sig{2} `>>>` 10 /\
  idx_leaf{2} = idx_sig{2} `&` (of_int (2 ^ 10 - 1))%W32 /\
  val root{2} = sub pk{1} 0 32 /\
  to_list root{1} = val _M'{2} /\
  
  
  address{2} = zero_address.[1 <- idx_tree{2}] /\

  to_uint t64{1} = 36 /\ 
  to_uint sm_offset{1} = 36
); first by auto.


(* Unroll the first iteration on the left hand side *)
unroll {1} 2.

(* inline {2} RootFromSig.rootFromSig. *)
(* Outline the inner loop *)
(* cf. https://github.com/EasyCrypt/easycrypt/wiki/%5BTactic%5D-Outline *)

rcondt {1} 2; first by auto.

seq 2 0 : (#pre /\ to_uint idx_leaf{1} = 2^10 - 1); first by auto.


qed.



(*
(* We have that sub sm_ptr 0 4 = W32ofBytes x.sig_idx => TODO: I need to write this lemma *)
    + admit.


swap {2} [2..3] -1.
seq 0 2 : (#pre /\ to_list pub_seed{1} = val seed{2}).
    + auto => /> &1 &2 ???? H*.
      apply (eq_from_nth witness); first by rewrite valP n_val size_to_list.
      rewrite size_to_list => j?.
      rewrite /EncodePkNoOID => />. 
      rewrite insubdK; first by rewrite /P size_sub // n_val. 
      by rewrite -get_to_list H.

(* This corresponds to memcpy(m + params->sig_bytes, sm + params->sig_bytes, *mlen)
   Lines  452 - 456 in the xmss_commons.jtmpl 
*)
seq 4 0 : (#pre).  (* this is irrelevant for the result of the proof => just stores *)
    + admit.


(* this conseq simplifies #pre so it fits on the screen *)
conseq (:
    Glob.mem{2} = mem /\
  (0 < to_uint (loadW64 Glob.mem{1} (to_uint ptr_mlen))  < W64.max_uint) /\
    mem_dif Glob.mem{1} Glob.mem{2} [to_uint mlen_ptr{1}] /\
    t64{1} = smlen{1} - (of_int XMSS_SIG_BYTES)%W64 /\
    m_ptr{1} = ptr_m /\
    mlen_ptr{1} = ptr_mlen /\
    sm_ptr{1} = ptr_sm /\
    smlen{1} = sm_len /\
    pk{1} = _pk /\
    pk{2} = EncodePkNoOID _pk /\
    m{2} = load_sig_mem mem ptr_sm sm_len /\
    s{2} = witness /\
    sm_offset{1} = W64.zero /\
    to_list pub_root{1} = sub pk{1} 0 32 /\
    to_list pub_seed{1} = sub pk{1} 32 32 /\
    
    ots_addr{1} = zero_address /\
    ltree_addr{1} = zero_address.[3 <- W32.one] /\
    node_addr{1} = zero_address.[3 <- W32.of_int 2]
  ==>
  _
).
    + auto => /> &1 &2 *; do split.
         * rewrite /zero_address tP => j?.
           rewrite initiE // /#.
         * rewrite /zero_address tP => j?.
           rewrite get_setE // initiE //.
           case (j = 3) => /#. 
         * rewrite /zero_address tP => j?.
           rewrite get_setE // initiE //.
           case (j = 3) => /#. 

(* This corresponds to the comment 
1) First we need to copy the randomness from sm + params->index_bytes to buf
*)
swap {2} 6 -5.
seq 3 1 : (
  #pre /\ 
  to_list buf{1} = val _R{2}
).
    + admit.

(* Unroll the first iteration on the left hand side *)
unroll {1} 9.


admit.
qed.
*)
