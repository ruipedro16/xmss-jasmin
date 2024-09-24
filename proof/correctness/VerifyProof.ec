pragma Goals : printall.

require import AllCore List RealExp IntDiv Distr DList IntDiv.

from Jasmin require import JModel JArray.

require import BitEncoding.
(*---*) import BitChunking.

require import Types Parameters Params Address Hash XMSS_MT_Params XMSS_MT_Types XMSS_MT_TreeHash XMSS_MT_PRF.
require import XMSS_IMPL.

require import Array32 Array64.

require import Correctness_Address.

require import Repr2.

(*
  args{1}:

  reg u64 m_ptr mlen_ptr,
  reg u64 sm_ptr smlen,
  reg ptr u8[XMSS_PK_BYTES] pk

  returns 0
*)

(*
  args{2}
  pk : xmss_pk
  m : msg_t
  s : sig_t
  
  returns true
*)

op load_buf (mem : global_mem_t) (ptr : W64.t) (inlen : W64.t) : W8.t list =
  mkseq (fun (i : int) => mem.[to_uint ptr + i]) (to_uint inlen).

op sig_size_bytes : int = 2500.

lemma size_bits_to_bytes (x : bool list):
    size (BitsToBytes x) = size x %/ 8.
proof.
rewrite /BitsToBytes size_map size_chunk //.
qed.

lemma size_lenbytes_be32_4 (x : W32.t) :
    size (lenbytes_be32 x 4) = 4.
proof.
rewrite /lenbytes_be32 size_rev size_take // size_bits_to_bytes size_w2bits //=.
qed.

lemma load_store_W64 (mem : global_mem_t) (a : address) (v : W64.t) :
    loadW64 (storeW64 mem a v) a = v.
proof.
rewrite /loadW64 pack8E /storeW64. 
admit.
qed.

lemma verify_correct (mem : global_mem_t) (mptr mlenptr smptr _smlen : W64.t, pkey : W8.t Array64.t):
    n = XMSS_N /\
    d = XMSS_D =>
    equiv[
        M(Syscall).__xmssmt_core_sign_open ~ XMSS_MT_PRF.verify : 
        Glob.mem{1} = mem /\
        Glob.mem{2} = mem /\
        arg{1} = (mptr, mlenptr, smptr, _smlen, pkey) /\
        arg{2}.`1 = EncodePkNoOID pkey /\
        arg{2}.`2 = load_buf mem mptr (loadW64 mem (to_uint mlenptr))
        ==> 
        res{2} <=> res{1} = W64.zero
    ].
proof.
rewrite /XMSS_N /XMSS_D.
move => [#] n_val d_val. 
proc.
seq 9 0 : #pre; first by auto.
seq 3 0 : (
  #pre /\ 
  to_uint sm_offset{1} = 0 /\
  to_list pub_root{1} = sub pk{1} 0 32 /\
  to_list pub_seed{1} = val pk{2}.`pk_pub_seed
).
    + auto => />.
      split.
          * apply (eq_from_nth witness); [by rewrite size_sub // size_to_list |]. 
            rewrite size_to_list => j?.             
            rewrite nth_sub // get_to_list initiE //.
          * apply (eq_from_nth witness); [by rewrite valP size_to_list n_val |]. 
            rewrite size_to_list => j?. 
            rewrite get_to_list initiE // /EncodePkNoOID => />. 
            rewrite insubdK; [by rewrite /P size_sub // n_val |]. 
            rewrite nth_sub //. 
swap {2} 4 -3. 
seq 1 1 : (
  #pre /\ 
  ots_addr{1} = zero_address /\
  address{2} = zero_address
).
    + inline {1} M(Syscall).__zero_address_.
      wp; sp.
      ecall {1} (zero_addr_res node_addr{1}).
      auto => />. 
seq 1 0 : (
  #pre /\ 
  ltree_addr{1} = zero_address
).
    + inline {1} M(Syscall).__zero_address_.
      wp; sp.
      ecall {1} (zero_addr_res ltree_addr{1}).
      auto => />.
seq 1 0 : (
  #pre /\ 
  node_addr{1} = zero_address
).
    + inline {1} M(Syscall).__zero_address_.
      wp; sp.
      ecall {1} (zero_addr_res node_addr{1}).
      auto => />.
seq 5 0 : (
(*  Glob.mem{1} = mem /\
  Glob.mem{2} = mem /\
*)
  m_ptr{1} = mptr /\
  mlen_ptr{1} = mlenptr /\
  sm_ptr{1} = smptr /\ 
  smlen{1} = _smlen /\ 
  pk{1} = pkey /\
  pk{2} = EncodePkNoOID pkey /\
  m{2} = load_buf mem mptr (loadW64 mem (to_uint mlenptr)) /\
  to_uint sm_offset{1} = 0 /\
  to_list pub_seed{1} = val pk{2}.`pk_pub_seed /\

  address{2} = zero_address /\

  ots_addr{1} = set_type zero_address 0 /\ 
  ltree_addr{1} = set_type zero_address 1 /\
  node_addr{1} = set_type zero_address 2 /\
  t64{1} = smlen{1} - W64.of_int 2500
); first by inline; auto => />.
seq 1 0 : (
  #pre /\
  loadW64 Glob.mem{1} (to_uint mlen_ptr{1}) = smlen{1} - W64.of_int 2500
).
    + auto => /> &1 *. 
      by rewrite load_store_W64.
seq 1 1 : (#pre /\ to_uint idx{1} = to_uint idx_sig{2}).
    + admit.
swap {2} 2 -1.
seq 0 1 : (#pre /\ val seed{2} = sub pk{1} 32 32).
    + auto => /> &1 &2 ????. 
      apply (eq_from_nth witness); [by rewrite size_sub // valP n_val |]. 
      rewrite valP n_val => j?.        
      rewrite nth_sub // /EncodePkNoOID => />.
      rewrite insubdK; [by rewrite /P size_sub // n_val |].
      rewrite nth_sub //.

seq 4 0 : (
  #pre /\
  load_buf Glob.mem{1} m_ptr{1} (of_int 2500)%W64 = load_buf Glob.mem{1} sm_ptr{1} (of_int 2500)%W64
).
    + admit.
seq 0 1 : (#pre /\ idx_bytes{2} = lenbytes_be32 idx_sig{2} 4); first by auto.

seq 3 0 : (
  #pre /\
  to_list buf{1} = val s{2}.`XMSS_MT_Types.r
).
    + admit. (* This requires the operator EncodeSignature *)

seq 0 2 : (
  #pre /\
  idx_tree{2} = idx_sig{2} `>>>` h /\
  idx_leaf{2} = idx_sig{2} `&` (of_int (2^h - 1))%W32
).
    + auto =>/> &1 &2 *.
      rewrite d_val //=.
seq 2 0 : (
  m_ptr{1} = mptr /\
  mlen_ptr{1} = mlenptr /\
  sm_ptr{1} = smptr /\
  smlen{1} = _smlen /\
  pk{1} = pkey /\
  pk{2} = EncodePkNoOID pkey /\
  m{2} = load_buf mem mptr (loadW64 mem (to_uint mlenptr)) /\
  to_uint sm_offset{1} = 0 /\
  to_list pub_seed{1} = val pk{2}.`pk_pub_seed /\
  address{2} = zero_address /\
  ots_addr{1} = set_type zero_address 0 /\
  ltree_addr{1} = set_type zero_address 1 /\
  node_addr{1} = set_type zero_address 2 /\
  loadW64 Glob.mem{1} (to_uint mlen_ptr{1}) =
  smlen{1} - (of_int 2500)%W64 /\
  to_uint idx{1} = to_uint idx_sig{2} /\
  val seed{2} = sub pk{1} 32 32 /\
  load_buf Glob.mem{1} m_ptr{1} ((of_int 2500))%W64 = load_buf Glob.mem{1} sm_ptr{1} ((of_int 2500))%W64 /\
  idx_bytes{2} = lenbytes_be32 idx_sig{2} 4 /\
  to_list buf{1} = val s{2}.`r /\
  idx_tree{2} = idx_sig{2} `>>>` h /\
  idx_leaf{2} = idx_sig{2} `&` (of_int (2 ^ h - 1))%W32 /\

  t64{1} = m_ptr{1} + W64.of_int 2372
); first by auto => />.
seq 0 3 : (
  #pre /\ 
  val root{2} = (sub pk{1} 0 32) /\
  (sig_ots{2}, auth{2}) = nth witness s{2}.`r_sigs 0 (* first reduced signature *) /\
  _R{2} = s{2}.`r
).
    + auto => /> &1 &2 *. 
      rewrite /EncodePkNoOID => />; split => [| /#].
      rewrite insubdK // /P size_sub // n_val //. 
seq 2 1 : (
  #pre /\
  bytes{1} = loadW64 Glob.mem{1} (to_uint mlen_ptr{1}) /\
  idx_hash{1} = idx{1} /\
  val t{2} = (val _R{2} ++ val root{2} ++ idx_bytes{2})
).
    + auto => /> &1 &2 *.
      admit.
seq 1 1 : (#pre /\ to_list root{1} = val _M'{2}). (* This root is the hash of the message *)
    + admit.

seq 2 0 : (  
     m_ptr{1} = mptr /\
     mlen_ptr{1} = mlenptr /\
     sm_ptr{1} = smptr /\
     smlen{1} = _smlen /\
     pk{1} = pkey /\
     pk{2} = EncodePkNoOID pkey /\
     m{2} = load_buf mem mptr (loadW64 mem (to_uint mlenptr)) /\
     to_uint sm_offset{1} =  36 /\
     to_list pub_seed{1} = val pk{2}.`pk_pub_seed /\
     address{2} = zero_address /\
     ots_addr{1} = set_type zero_address 0 /\
     ltree_addr{1} = set_type zero_address 1 /\
     node_addr{1} = set_type zero_address 2 /\
     loadW64 Glob.mem{1} (to_uint mlen_ptr{1}) = smlen{1} - (of_int 2500)%W64 /\
     to_uint idx{1} = to_uint idx_sig{2} /\
     val seed{2} = sub pk{1} 32 32 /\
     load_buf Glob.mem{1} m_ptr{1} ((of_int 2500))%W64 =
     load_buf Glob.mem{1} sm_ptr{1} ((of_int 2500))%W64 /\
     idx_bytes{2} = lenbytes_be32 idx_sig{2} 4 /\
     to_list buf{1} = val s{2}.`r /\
     idx_tree{2} = idx_sig{2} `>>>` h /\
     idx_leaf{2} = idx_sig{2} `&` (of_int (2 ^ h - 1))%W32 /\
    val root{2} = sub pk{1} 0 32 /\
    (sig_ots{2}, auth{2}) = nth witness s{2}.`r_sigs 0 /\ _R{2} = s{2}.`r /\
   bytes{1} = loadW64 Glob.mem{1} (to_uint mlen_ptr{1}) /\
   idx_hash{1} = idx{1} /\
   val t{2} = val _R{2} ++ val root{2} ++ idx_bytes{2} /\
  to_list root{1} = val _M'{2}
).
    + auto => /> &1 &2 H *.
      rewrite to_uintD H of_uintK /#.  
(* handle the results here *)
seq 2 5 : (
  pk{2} = EncodePkNoOID pk{1} /\
  to_list pub_root{1} = sub pk{1} 0 32 /\
  to_list root{1} = val root{2}
); last first.
    + admit.
seq 0 2 : (
  m_ptr{1} = mptr /\
  mlen_ptr{1} = mlenptr /\
  sm_ptr{1} = smptr /\
  smlen{1} = _smlen /\
  pk{1} = pkey /\
  pk{2} = EncodePkNoOID pkey /\
  m{2} = load_buf mem mptr (loadW64 mem (to_uint mlenptr)) /\
  to_uint sm_offset{1} = 36 /\
  to_list pub_seed{1} = val pk{2}.`pk_pub_seed /\
  ots_addr{1} = set_type zero_address 0 /\
  ltree_addr{1} = set_type zero_address 1 /\
  node_addr{1} = set_type zero_address 2 /\
  loadW64 Glob.mem{1} (to_uint mlen_ptr{1}) = smlen{1} - (of_int 2500)%W64 /\
  to_uint idx{1} = to_uint idx_sig{2} /\
  val seed{2} = sub pk{1} 32 32 /\
  load_buf Glob.mem{1} m_ptr{1} ((of_int 2500))%W64 =
  load_buf Glob.mem{1} sm_ptr{1} ((of_int 2500))%W64 /\
  idx_bytes{2} = lenbytes_be32 idx_sig{2} 4 /\
  to_list buf{1} = val s{2}.`r /\
  idx_tree{2} = idx_sig{2} `>>>` h /\
  idx_leaf{2} = idx_sig{2} `&` (of_int (2 ^ h - 1))%W32 /\
  val root{2} = sub pk{1} 0 32 /\
  (sig_ots{2}, auth{2}) = nth witness s{2}.`r_sigs 0 /\
  _R{2} = s{2}.`r /\
  bytes{1} = loadW64 Glob.mem{1} (to_uint mlen_ptr{1}) /\
  idx_hash{1} = idx{1} /\
  val t{2} = val _R{2} ++ val root{2} ++ idx_bytes{2} /\
  to_list root{1} = val _M'{2} /\

  address{2} = set_tree_addr (set_layer_addr zero_addr 0) (to_uint idx_tree{2})
); first by auto => />.
qed.
