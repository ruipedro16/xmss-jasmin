pragma Goals : printall.

require import AllCore List RealExp IntDiv Distr DList IntDiv.
from Jasmin require import JModel JArray.

require import Params Types Address Hash XMSS_MT_Params WOTS LTree XMSS_MT_TreeHash XMSS_MT_Types XMSS_MT_PRF.
require import XMSS_IMPL Parameters.

require import Repr2 Utils2.

require import Array4 Array8 Array32 Array64 Array68 Array96 Array352 Array2144.

require import Correctness_Address Correctness_Bytes Correctness_Mem Correctness_Hash.
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
      arg.`1 = eq /\
      0 <= to_uint (loadW64 Glob.mem (to_uint mlen_ptr)) < W64.max_uint
      ==>
      (eq = W8.zero) => res = W64.zero /\
      (eq <> W8.zero) => res = W64.of_int (-1)
    ] = 1%r.
proof.
by conseq set_result_ll (set_result_post eq); auto.
qed.


(*

arg{1}

m_ptr : W64.t         => ptr to the message 
mlen_ptr : W64.t      => ptr to the message length 
sm_ptr : W64.t        => ptr to the signed message ( signed message = signature ++ message )
smlen : W64.t         => length of the signed message = mlen + sig bytes
pk : W8.t Array64.t   => public key

arg{2}

pk : xmss_pk  => public key 
m : msg_t     => message 
s : sig_t    => signature How to encode signature ?
*)

(* Load the signature from memory. Ignores the message *)
op load_sig_mem (mem : global_mem_t) (sm_ptr sm_len : W64.t) : W8.t list =
    mkseq (fun (i : int) => loadW8 mem (to_uint sm_ptr + i)) XMSS_SIG_BYTES.

lemma verify_correctness (mem : global_mem_t)  (ptr_m ptr_mlen ptr_sm sm_len : W64.t) (_pk : W8.t Array64.t) :
    n = XMSS_N /\
    d = XMSS_D /\
    h = XMSS_FULL_HEIGHT =>
    equiv [
      M(Syscall).__xmssmt_core_sign_open ~ XMSS_MT_PRF.verify :
      
      Glob.mem{1} = mem /\

      0 < to_uint (loadW64 mem (to_uint ptr_mlen)) < W64.max_uint /\
      valid_ptr_i ptr_sm 36 /\
      valid_ptr_i ptr_m 2372 /\

      XMSS_SIG_BYTES < to_uint sm_len /\

      arg{1} = (ptr_m, ptr_mlen, ptr_sm, sm_len, _pk) /\
      arg{2}.`1 = EncodePkNoOID _pk /\
      arg{2}.`2 = load_sig_mem mem ptr_sm sm_len /\
      arg{2}.`3 = EncodeSignature ( load_signature_mem mem ptr_sm (sm_len - W64.of_int XMSS_SIG_BYTES) )
      ==>
      (res{2} <=> res{1} = W64.zero) 
    ].
proof.
rewrite /XMSS_N /XMSS_D /XMSS_FULL_HEIGHT => [#] n_val d_val h_val.
proc => /=. 
seq 9 0 : #pre; first by auto.
ecall {1} (p_set_result_post are_equal{1}).
conseq />; first by smt().
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

seq 3 0 : (
    #pre /\
    ots_addr{1} = zero_address /\ 
    ltree_addr{1} = zero_address /\ 
    node_addr{1} = zero_address 
).
    + inline {1} 3; wp; ecall {1} (zero_addr_res addr{1}); wp.
      inline {1} 2; wp; ecall {1} (zero_addr_res addr{1}); wp.
      inline {1} 1; wp; ecall {1} (zero_addr_res addr{1}); wp.
      skip => />.

seq 1 0 : (#pre /\ ots_addr{1}.[3] = W32.zero).
    + inline {1}; auto => /> &1 *; by apply zero_addr_setZero.

seq 1 0 : (
  #{/~ltree_addr{1} = zero_address}pre /\
  sub ltree_addr{1} 0 2 = nseq 2 W32.zero /\
  ltree_addr{1}.[3] = W32.one /\
  sub ltree_addr{1} 4 4 = nseq 4 W32.zero
).
    + inline {1}; auto => /> &1 *.
      split; (
         apply (eq_from_nth witness); [by rewrite size_sub // size_nseq | rewrite size_sub // => i?];
         rewrite nth_sub // nth_nseq //= get_setE // ifF 1:/# zero_addr_i /#
      ).

seq 1 0 : (
  #{/~node_addr{1} = zero_address}pre /\
  sub node_addr{1} 0 2 = nseq 2 W32.zero /\
  node_addr{1}.[3] = W32.of_int 2 /\
  sub node_addr{1} 4 4 = nseq 4 W32.zero
).
    + inline {1}; auto => /> &1 *.
      split; (
         apply (eq_from_nth witness); [by rewrite size_sub // size_nseq | rewrite size_sub // => i?];
         rewrite nth_sub // nth_nseq //= get_setE // ifF 1:/# zero_addr_i /#
      ).

seq 2 0 : (#pre /\ to_uint t64{1} = to_uint smlen{1} - XMSS_SIG_BYTES).
    + auto => /> &1 *.
      rewrite /XMSS_SIG_BYTES to_uintB 2:/# uleE /#.

swap {2} 4 -3.
seq 0 1 : (#pre /\ address{2} = zero_address); first by auto.

seq 1 0 : (
  #{/~Glob.mem{1} = mem}
   {/~to_uint t64{1} = to_uint smlen{1} - XMSS_SIG_BYTES}pre /\ 
  to_uint (loadW64 Glob.mem{1} (to_uint mlen_ptr{1})) = to_uint smlen{1} - XMSS_SIG_BYTES
); first by auto => /> &1 *; by rewrite load_store_W64.

seq 1 1 : (#pre /\ to_uint idx{1} = to_uint idx_sig{2}).
    + ecall {1} (bytes_to_ull_ptr_correct Glob.mem{1} sm_ptr{1}).
      auto => /> &1 *.
      split => [/# |].
      move => ??.
      rewrite /EncodeSignature => />.
      admit.

swap {2} 2 -1.
seq 0 1 : (#pre /\ val seed{2} = sub pk{1} 32 32).
  + auto => /> &1 &2 *.
    rewrite /EncodePkNoOID => />.
    rewrite insubdK // /P size_sub /#.

swap {2} 5 -4.
seq 0 1 : (#pre /\ val root{2} = sub pk{1} 0 32).
  + auto => /> &1 &2 *.
    rewrite /EncodePkNoOID => />.
    rewrite insubdK // /P size_sub /#.

swap {2} 5 -4.
seq 0 1 : (
  #pre /\ 
  val _R{2} = sub_list ((load_signature_mem mem ptr_sm (sm_len - (of_int XMSS_SIG_BYTES)%W64))) XMSS_INDEX_BYTES 32
).
    + auto => /> &1 &2 *.
      rewrite /EncodeSignature => />.
      rewrite insubdK // /P size_sub_list /#.


(* This seq corresponds to memcpy(m + params->sig_bytes, sm + params->sig_bytes, *mlen); *)
seq 4 0 : (
    #pre 
); first by admit.

(* After this seq, buf contains sm + params->index_bytes = _R{2} *)
seq 2 0 : (
  #pre /\ to_list buf{1} = val _R{2}
); first by admit.



(* This corresponds to *mlen = smlen - params->sig_bytes; *)
seq 3 0 : (
  (0 < to_uint (loadW64 mem (to_uint ptr_mlen))  < W64.max_uint) /\

    valid_ptr_i ptr_sm 36 /\
      valid_ptr_i ptr_m 2372 /\

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
  node_addr{1} = zero_address.[3 <- (of_int 2)%W32] /\


  loadW64 Glob.mem{1} (to_uint mlen_ptr{1}) = smlen{1} - (W64.of_int 2500) /\
      XMSS_SIG_BYTES < to_uint sm_len{1}
).
    + auto => /> &1 *.
      by rewrite load_store_W64.

seq 1 2 : (
  #pre /\ 
  to_uint idx{1} = to_uint idx_sig{2} /\
  idx_sig{2} = s{2}.`sig_idx
).
    + auto => />.
      ecall {1} (bytes_to_ull_ptr_correct Glob.mem{1} sm_ptr{1}).
      auto => /> &1 *; split; first by smt(@W64 pow2_64).
      move => *.
      rewrite /EncodeSignature => />.
      rewrite W64_W32_of_bytes; [ by rewrite size_sub_list |].  
      congr. 
      rewrite wordP => j?.
      rewrite /W64ofBytes /bits2w !initiE // => />.
      rewrite /concatMap.
      (* a partir daqui esta mal *)
      rewrite !(nth_flatten false 8).
          * pose P := (fun (s : bool list) => size s = 8).
            pose L := (map W8.w2bits (mkseq (fun (i0 : int) => loadW8 Glob.mem{1} (to_uint ptr_sm + i0)) 4)).
            rewrite -(all_nthP P L witness) /P /L size_map size_mkseq (: max 0 4 = 4) // => i?. 
            rewrite (nth_map witness); first by rewrite size_mkseq //.
            rewrite /w2bits size_mkseq //.
          * pose P := (fun (s : bool list) => size s = 8).
            pose L := (map W8.w2bits (sub_list (load_signature_mem mem ptr_sm (sm_len - (of_int XMSS_SIG_BYTES)%W64)) 0 4)).
            rewrite -(all_nthP P L witness) /P /L size_map size_mkseq (: max 0 4 = 4) // => i?. 
            rewrite (nth_map witness); first by rewrite size_mkseq //.
            rewrite /w2bits size_mkseq //.
      rewrite !(nth_map witness). 
          * rewrite size_mkseq. admit.
          * rewrite size_iota. admit.
          * rewrite size_sub_list //. admit.
          * rewrite size_iota. admit.
      rewrite /w2bits nth_mkseq 1:/# nth_mkseq 1:/# => />.
      rewrite /load_signature_mem nth_mkseq nth_iota.
          * admit.
          * smt(). 
          * admit.
      admit.

(* This corresponds to the comment 

    /* Put the message all the way at the end of the m buffer, so that we can
     * prepend the required other inputs for the hash function. */      
    
    This is not useful for the proof 
*)
seq 4 0 : (#pre). 
    + seq 3 0 : (#pre /\ 0 <= to_uint bytes{1} < W64.max_uint).
         * auto => /> &1 ???????? -> *; split => [| ?]. 
              - smt(@W64 pow2_64).
              - rewrite to_uintB; [by rewrite uleE of_uintK /= /# |]. 
                rewrite of_uintK /= #smt:(@W64 pow2_64).
      inline {1}.
      while {1} (#post) (to_uint bytes2{1} - to_uint i0{1}); last by auto => /> *; rewrite ultE /#.
      admit.
  
seq 0 2 : (
    #pre /\
    val seed{2} = to_list pub_seed{1} /\
    address{2} = zero_address
).
    + auto => /> &1 &2 ?????? -> *. 
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
    + auto => /> &1 &2 ???????????? ->. 
(* A seta refere se a hipotese to_list buf{1} =
   mkseq (fun (i0 : int) => loadW8 Glob.mem{1} (to_uint ptr_sm + 4 + i0)) 32
*)

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
    + auto => /> &1 &2 ???????? -> *; split.
(* A seta refere se a hipotese loadW64 Glob.mem{1} (to_uint ptr_mlen) = sm_len - (of_int 2500)%W64 *)
        * rewrite to_uintD of_uintK /= /#. 
        * rewrite /XMSS_SIG_BYTES to_uintB.
             - rewrite uleE of_uintK /= /#.
          rewrite of_uintK /#.

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

(* #pre but update sm_offset *) 
seq 2 1 : (
  0 < to_uint (loadW64 mem (to_uint ptr_mlen)) < W64.max_uint /\
  valid_ptr_i ptr_sm 36 /\
  valid_ptr_i ptr_m 2372 /\
  m_ptr{1} = ptr_m /\
  mlen_ptr{1} = ptr_mlen /\
  sm_ptr{1} = ptr_sm /\
  smlen{1} = sm_len /\
  pk{1} = _pk /\
  pk{2} = EncodePkNoOID _pk /\
  m{2} = load_sig_mem mem ptr_sm sm_len /\
  s{2} = EncodeSignature (load_signature_mem mem ptr_sm (sm_len - (of_int XMSS_SIG_BYTES)%W64)) /\
  to_list pub_root{1} = sub pk{1} 0 32 /\
  to_list pub_seed{1} = sub pk{1} 32 32 /\
  ots_addr{1} = zero_address /\
  ltree_addr{1} = zero_address.[3 <- W32.one] /\
  node_addr{1} = zero_address.[3 <- (of_int 2)%W32] /\
  loadW64 Glob.mem{1} (to_uint mlen_ptr{1}) = smlen{1} - (of_int 2500)%W64 /\ 
  XMSS_SIG_BYTES < to_uint sm_len /\ 
  to_uint idx{1} = to_uint idx_sig{2} /\ 
  idx_sig{2} = s{2}.`sig_idx /\
  val seed{2} = to_list pub_seed{1} /\
  address{2} = zero_address /\
  to_list buf{1} = mkseq (fun (i0 : int) => loadW8 Glob.mem{1} (to_uint sm_ptr{1} + 4 + i0)) 32 /\
  to_list buf{1} = val _R{2} /\
  to_uint bytes{1} = to_uint smlen{1} - XMSS_SIG_BYTES /\
  idx_tree{2} = idx_sig{2} `>>>` 10 /\
  idx_leaf{2} = idx_sig{2} `&` (of_int (2 ^ 10 - 1))%W32 /\
  val root{2} = sub pk{1} 0 32 /\
  to_list root{1} = val _M'{2} /\

  to_uint sm_offset{1} = 4 + 32
).
    + auto => /> &1 &2 *.
      rewrite /set_layer_addr /zero_address tP => j?.
      rewrite get_setE // .
      case (j = 0) => [? | //]. 
      by rewrite initiE.

(* #pre but update address{2} *)


seq 0 1 : (
  0 < to_uint (loadW64 mem (to_uint ptr_mlen)) < W64.max_uint /\
  valid_ptr_i ptr_sm 36 /\
  valid_ptr_i ptr_m 2372 /\
  m_ptr{1} = ptr_m /\
  mlen_ptr{1} = ptr_mlen /\
  sm_ptr{1} = ptr_sm /\
  smlen{1} = sm_len /\
  pk{1} = _pk /\
  pk{2} = EncodePkNoOID _pk /\
  m{2} = load_sig_mem mem ptr_sm sm_len /\
  s{2} = EncodeSignature (load_signature_mem mem ptr_sm (sm_len - (of_int XMSS_SIG_BYTES)%W64)) /\
  to_list pub_root{1} = sub pk{1} 0 32 /\
  to_list pub_seed{1} = sub pk{1} 32 32 /\
  ots_addr{1} = zero_address /\
  ltree_addr{1} = zero_address.[3 <- W32.one] /\
  node_addr{1} = zero_address.[3 <- (of_int 2)%W32] /\
  loadW64 Glob.mem{1} (to_uint mlen_ptr{1}) = smlen{1} - (of_int 2500)%W64 /\ 
  XMSS_SIG_BYTES < to_uint sm_len /\ 
  to_uint idx{1} = to_uint idx_sig{2} /\ 
  idx_sig{2} = s{2}.`sig_idx /\
  val seed{2} = to_list pub_seed{1} /\
  to_list buf{1} = mkseq (fun (i0 : int) => loadW8 Glob.mem{1} (to_uint sm_ptr{1} + 4 + i0)) 32 /\
  to_list buf{1} = val _R{2} /\
  to_uint bytes{1} = to_uint smlen{1} - XMSS_SIG_BYTES /\
  idx_tree{2} = idx_sig{2} `>>>` 10 /\
  idx_leaf{2} = idx_sig{2} `&` (of_int (2 ^ 10 - 1))%W32 /\
  val root{2} = sub pk{1} 0 32 /\
  to_list root{1} = val _M'{2} /\

  to_uint sm_offset{1} = 4 + 32 /\

  address{2} = set_tree_addr zero_address (to_uint (s{2}.`sig_idx `>>>` 10))
); first by auto.  

unroll {1} 2.
rcondt {1} 2; first by auto.

seq 3 0 : (
  #pre /\
  i{1} = W32.zero /\
  idx_leaf{1} = (of_int (2^10 - 1))%W32 `&` (truncateu32 idx{1})
); first by auto.

swap{1} 3.

seq 3 0 : (#pre).
    + inline {1}; auto => /> *.
      do split.
          * by apply zero_addr_setZero.
          * rewrite tP => j?.
            rewrite get_setE //.
            case (j = 0) => ?; last by rewrite get_setE.
            by rewrite get_setE // ifF 1:/# zero_addr_i.
          * rewrite tP => j?.
            rewrite get_setE //.
            case (j = 0) => ?; last by rewrite get_setE.
            by rewrite get_setE // ifF 1:/# zero_addr_i.
          
(** ------------------------------------------------------------------------------------------------------------------------------------------------ **)

seq 24 4 : (
0 <= to_uint (loadW64 Glob.mem{1} (to_uint mlen_ptr{1})) < W64.max_uint /\
val node{2} = to_list root{1} /\
val root{2} = to_list pub_root{1} /\
is_valid{2} = (are_equal{1} = W8.zero)
); last first.

    + case (root{1} = pub_root{1}).
         * seq 1 0 : (val node{2} = to_list root{1} /\
                      val root{2} = to_list pub_root{1} /\
                      root{1} = pub_root{1} /\ 
                      0 <= to_uint (loadW64 Glob.mem{1} (to_uint mlen_ptr{1})) < W64.max_uint /\ 
                      are_equal{1} = W8.zero).
               - exists * root{1}, pub_root{1}.
                 elim * => P0 P1.
                 call {1} (p_memcmp_true P0 P1); last by auto.
                 admit. (* Nao percebi => Quando chego a este subgoal ja nao ha informacao sobre P0 e P1 *)     
           ecall {1} (p_set_result_post are_equal{1}).
           auto => /> &1 &2 H0 H1 *.
           do split.
               - admit.
               - apply nbytes_eq. 
                 by rewrite H0 H1.

         * seq 1 0 : (val node{2} = to_list root{1} /\
                      val root{2} = to_list pub_root{1} /\
                      root{1} <> pub_root{1} /\ 
                      0 <= to_uint (loadW64 Glob.mem{1} (to_uint mlen_ptr{1})) < W64.max_uint /\ are_equal{1} 
                      <> W8.zero).
               - exists * root{1}, pub_root{1}.
                 elim * => P0 P1.
                 call {1} (p_memcmp_false P0 P1); last by auto.
                 admit. (* Nao percebi => Quando chego a este subgoal ja nao ha informacao sobre P0 e P1 *)     
           ecall {1} (p_set_result_post are_equal{1}).
           auto => /> &1 &2 H0 H1*.
           do split => [* |].
               - admit.
               - apply nbytes_eq. 
                 rewrite H0 H1.
                 admit. (* This is false *)

(** ------------------------------------------------------------------------------------------------------------------------------------------------ **)

(* Replaced truncateu32 idx{1} with idx_sig{2} *)
seq 1 0 : (
    0 < to_uint (loadW64 mem (to_uint ptr_mlen)) < W64.max_uint /\
    valid_ptr_i ptr_sm 36 /\
    valid_ptr_i ptr_m 2372 /\
    m_ptr{1} = ptr_m /\
    mlen_ptr{1} = ptr_mlen /\
    sm_ptr{1} = ptr_sm /\
    smlen{1} = sm_len /\
    pk{1} = _pk /\
    pk{2} = EncodePkNoOID _pk /\
    m{2} = load_sig_mem mem ptr_sm sm_len /\
    s{2} = EncodeSignature (load_signature_mem mem ptr_sm (sm_len - (of_int XMSS_SIG_BYTES)%W64)) /\
    to_list pub_root{1} = sub pk{1} 0 32 /\
    to_list pub_seed{1} = sub pk{1} 32 32 /\
    ots_addr{1} = zero_address /\
    ltree_addr{1} = zero_address.[3 <- W32.one] /\
    node_addr{1} = zero_address.[3 <- (of_int 2)%W32] /\
    loadW64 Glob.mem{1} (to_uint mlen_ptr{1}) = smlen{1} - (of_int 2500)%W64 /\
    XMSS_SIG_BYTES < to_uint sm_len /\
    idx_sig{2} = s{2}.`sig_idx /\
    val seed{2} = to_list pub_seed{1} /\
    to_list buf{1} = mkseq (fun (i0 : int) => loadW8 Glob.mem{1} (to_uint sm_ptr{1} + 4 + i0)) 32 /\
    to_list buf{1} = val _R{2} /\
    to_uint bytes{1} = to_uint smlen{1} - XMSS_SIG_BYTES /\
    idx_tree{2} = idx_sig{2} `>>>` 10 /\
    idx_leaf{2} = idx_sig{2} `&` (of_int (2 ^ 10 - 1))%W32 /\
    val root{2} = sub pk{1} 0 32 /\
    to_list root{1} = val _M'{2} /\
    to_uint sm_offset{1} = 4 + 32 /\
    address{2} = set_tree_addr zero_address (to_uint (s{2}.`sig_idx `>>>` 10)) /\
    i{1} = W32.zero /\
    idx_leaf{1} = (of_int (2 ^ 10 - 1))%W32 `&` idx_sig{2} /\


    (* neste shift substitui idx{1} : W64.t por zeroextu64 idx_sig{2} *)  
    idx{1} = zeroextu64 idx_sig{2} `>>` truncateu8 (W256.of_int 10 `&` W256.of_int 63)
).
    + auto => /> &1 &2 *; split.
         * congr.
           rewrite /EncodeSignature /load_signature_mem => />.
           rewrite wordP => j?.
           admit.
         * congr.  
           rewrite /EncodeSignature /load_signature_mem => />.
           rewrite wordP => j?.
           admit.

seq 4 0 : (
    0 < to_uint (loadW64 mem (to_uint ptr_mlen)) < W64.max_uint /\
    valid_ptr_i ptr_sm 36 /\
    valid_ptr_i ptr_m 2372 /\
    m_ptr{1} = ptr_m /\
    mlen_ptr{1} = ptr_mlen /\
    sm_ptr{1} = ptr_sm /\
    smlen{1} = sm_len /\
    pk{1} = _pk /\
    pk{2} = EncodePkNoOID _pk /\
    m{2} = load_sig_mem mem ptr_sm sm_len /\
    s{2} = EncodeSignature (load_signature_mem mem ptr_sm (sm_len - (of_int XMSS_SIG_BYTES)%W64)) /\
    to_list pub_root{1} = sub pk{1} 0 32 /\
    to_list pub_seed{1} = sub pk{1} 32 32 /\
    loadW64 Glob.mem{1} (to_uint mlen_ptr{1}) = smlen{1} - (of_int 2500)%W64 /\
    XMSS_SIG_BYTES < to_uint sm_len /\
    idx_sig{2} = s{2}.`sig_idx /\
    val seed{2} = to_list pub_seed{1} /\
    to_list buf{1} = mkseq (fun (i0 : int) => loadW8 Glob.mem{1} (to_uint sm_ptr{1} + 4 + i0)) 32 /\
    to_list buf{1} = val _R{2} /\
    to_uint bytes{1} = to_uint smlen{1} - XMSS_SIG_BYTES /\
    idx_tree{2} = idx_sig{2} `>>>` 10 /\
    idx_leaf{2} = idx_sig{2} `&` (of_int (2 ^ 10 - 1))%W32 /\
    val root{2} = sub pk{1} 0 32 /\
    to_list root{1} = val _M'{2} /\
    to_uint sm_offset{1} = 4 + 32 /\
    address{2} = set_tree_addr zero_address (to_uint (s{2}.`sig_idx `>>>` 10)) /\
    i{1} = W32.zero /\
    idx_leaf{1} = (of_int (2 ^ 10 - 1))%W32 `&` idx_sig{2} /\

    idx{1} = zeroextu64 idx_sig{2} `>>` truncateu8 (W256.of_int 10 `&` W256.of_int 63) /\

    ots_addr{1} = set_tree_addr (set_tree_addr zero_address (to_uint idx{1})) (to_uint idx_leaf{1}) /\
    ltree_addr{1} = set_tree_addr (zero_address.[3 <- W32.one]) (to_uint idx{1}) /\
    node_addr{1} = set_tree_addr (zero_address.[3 <- (of_int 2)%W32]) (to_uint idx{1})
).
    + inline {1}.
      auto => /> &1 &2 *.
      admit.


conseq (:
    0 < to_uint (loadW64 mem (to_uint ptr_mlen)) < W64.max_uint /\
    valid_ptr_i ptr_sm 36 /\
    valid_ptr_i ptr_m 2372 /\
    m_ptr{1} = ptr_m /\
    mlen_ptr{1} = ptr_mlen /\
    sm_ptr{1} = ptr_sm /\
    smlen{1} = sm_len /\
    pk{1} = _pk /\
    pk{2} = EncodePkNoOID _pk /\
    m{2} = load_sig_mem mem ptr_sm sm_len /\
    s{2} = EncodeSignature (load_signature_mem mem ptr_sm (sm_len - (of_int XMSS_SIG_BYTES)%W64)) /\
    to_list pub_root{1} = sub pk{1} 0 32 /\
    to_list pub_seed{1} = sub pk{1} 32 32 /\
    loadW64 Glob.mem{1} (to_uint mlen_ptr{1}) = smlen{1} - (of_int 2500)%W64 /\
    XMSS_SIG_BYTES < to_uint sm_len /\
    idx_sig{2} = s{2}.`sig_idx /\
    val seed{2} = to_list pub_seed{1} /\
    to_list buf{1} = mkseq (fun (i0 : int) => loadW8 Glob.mem{1} (to_uint sm_ptr{1} + 4 + i0)) 32 /\
    to_list buf{1} = val _R{2} /\
    to_uint bytes{1} = to_uint smlen{1} - XMSS_SIG_BYTES /\
    idx_tree{2} = idx_sig{2} `>>>` 10 /\
    idx_leaf{2} = idx_sig{2} `&` (of_int (2 ^ 10 - 1))%W32 /\
    val root{2} = sub pk{1} 0 32 /\
    to_list root{1} = val _M'{2} /\
    to_uint sm_offset{1} = 4 + 32 /\
    address{2} = set_tree_addr zero_address (to_uint (s{2}.`sig_idx `>>>` 10)) /\
    i{1} = W32.zero /\
    idx_leaf{1} = (of_int (2 ^ 10 - 1))%W32 `&` idx_sig{2} /\

    idx{1} = zeroextu64 idx_sig{2} `>>` truncateu8 (W256.of_int 10 `&` W256.of_int 63) /\

    (* This was simplified using lemma set_tree_addr_comp *)
    ots_addr{1} = set_tree_addr zero_address (to_uint idx_leaf{1}) /\
    ltree_addr{1} = set_tree_addr (zero_address.[3 <- W32.one]) (to_uint idx{1}) /\
    node_addr{1} = set_tree_addr (zero_address.[3 <- (of_int 2)%W32]) (to_uint idx{1})

  ==>
  _
).
    + auto => /> &1 &2 *.
      rewrite set_tree_addr_comp //.

seq 2 1 : (
  #pre /\
  t64{1} = sm_ptr{1} + sm_offset{1} /\
  (sig_ots{2}, auth{2}) = nth witness s{2}.`r_sigs 0
); first by auto => /> /#.

inline {2} 1.

seq 1 0 : #pre; first by auto.


seq 0 6 : (
  #pre /\
  idx_sig0{2} = idx_leaf{2} /\                           
  sig_ots0{2} = sig_ots{2} /\
  auth0{2} = auth{2} /\
  M{2} = _M'{2} /\                             
  _seed{2} = seed{2} /\
  address0{2} = address{2}
);first by auto.

seq 0 2 : (
    #{/~address0{2} = address{2}}pre /\
  address0{2} = set_ots_addr (set_tree_addr zero_address (to_uint (s{2}.`sig_idx `>>>` 10))) (to_uint idx_sig{2})
).
    + auto => /> &1 &2 *.
      rewrite tP => j?.
      do 2! congr; last first.
        * admit.
      rewrite /set_type /set_tree_addr.
      admit.







(* #pre no longer holds : the value of root was changed *)
seq 1 1 : (
    #{/~to_list root{1} = val _M'{2}}
     {/~ots_addr{1} = set_tree_addr zero_address (to_uint idx_leaf{1})}pre /\
      wots_pk{1} = DecodeWotsPk pk_ots{2}
(*     ots_addr{1}.[0-4]   ====> cf. Properties Address *)
).
    + admit.
  

seq 2 0 : (
  #{/~t64{1} = sm_ptr{1} + sm_offset{1}}pre /\
  to_uint t64{1} = 2180 
). 
    + auto => /> &1 &2 ??????????????? H?.
      rewrite to_uintD_small; [by rewrite H of_uintK |].
      by rewrite H of_uintK /=.
seq 1 0 : (#{/~to_uint sm_offset{1} = 4 + 32}pre /\ sm_offset{1} = t64{1}); first by auto.

(* Not sure if #pre is preserved *)
seq 2 3 : (#pre /\ to_list leaf{1} = val nodes0{2}).
    + admit.

(* https://github.com/EasyCrypt/easycrypt/wiki/%5BTactic%5D-Outline *)
outline {2} [3-4] (node) <@ RootFromSig_Hop.rootFromSigInnerLoop; last first.    (* So quero substituir isto do lado direito *)
                                                                                 (* Nao percebi pq esta a gerar um subgoal com a substituicao feita do lado esquedo ? *)
    + admit.
 
seq 4 0 : (
    #{/~to_uint t64{1} = 2180}
     {/~sm_offset{1} = t64{1}}pre  /\
    t64{1} = sm_ptr{1} + W64.of_int 2180 /\
    sm_offset{1} = W64.of_int 2180
); first by auto => /> *; split; smt(@W64 pow2_64).

seq 1 3 : (
  #pre
).

