pragma Goals : printall.

require import AllCore List RealExp IntDiv Distr DList.

from Jasmin require import JModel.

require import Params Address Hash WOTS LTree XMSS_MT_TreeHash.
require import XMSS_IMPL Parameters.
require import Repr2.

require import Array32 Array64.

require import Correctness_Mem.

module RootFromSig_Hop = {
  proc rootFromSigInnerLoop (nodes0 : nbytes, idx_sig : W32.t, _seed : seed, auth : auth_path, address : adrs) : nbytes = {
    var k : int;
    var nodes1 : nbytes;
    var index : int;
    var auth_k : nbytes;

    k <- 0;
    while (k < h) {
      address <- set_tree_height address k;

      if (floor ((W32.to_uint idx_sig)%r / (2^k)%r) %% 2 = 0) {
        index <- get_tree_index address;
        address <- set_tree_index address (index %/ 2);

        auth_k <- nth witness (val auth) k;
        nodes1 <@ Hash.rand_hash (nodes0, auth_k, _seed, address);
      } else {
        index <- get_tree_index address;
        address <- set_tree_index address ((index - 1) %/ 2);

        auth_k <- nth witness (val auth) k;
        nodes1 <@ Hash.rand_hash (auth_k, nodes0, _seed, address);
      }

      nodes0 <- nodes1;
      k <- k + 1;
    }

    return nodes0;
  } 

  proc rootFromSig(idx_sig : W32.t, sig_ots : wots_signature, auth : auth_path, M : nbytes, 
                   _seed : seed, address : adrs) : nbytes = {
    var pk_ots : wots_pk;
    var nodes0, nodes1 : nbytes;
    
    address <- set_type address 0;
    address <- set_ots_addr address (W32.to_uint idx_sig);

    pk_ots <@ WOTS.pkFromSig(M, sig_ots, _seed, address);

    address <- set_type address 1;
    address <- set_ltree_addr address (W32.to_uint idx_sig);

    nodes0 <@ LTree.ltree(pk_ots, address, _seed);

    address <- set_type address 2;
    address <- set_tree_index address (W32.to_uint idx_sig);

    nodes0 <@ rootFromSigInnerLoop (nodes0, idx_sig, _seed, auth, address);

    return nodes0;
  }
}.

equiv rootFromSigHop : 
    RootFromSig_Hop.rootFromSig ~ RootFromSig.rootFromSig : ={arg} ==> ={res}.
proof.
proc.
inline {1} RootFromSig_Hop.rootFromSigInnerLoop.
sim => />.
qed.

lemma rootFromSigCorrectness mem :
    equiv [
      M(Syscall).__compute_root ~ RootFromSig_Hop.rootFromSigInnerLoop :
      Glob.mem{1} = mem /\
      Glob.mem{2} = mem

      (* valid ptr auth path 32 *)
      ==>
      false
    ].
proof.
proc.
seq 5 0 : (
  #pre /\
  auth_path_ptr{1} = _auth_path_ptr{1} /\
  t32{1} = leaf_idx{1} `&` W32.one
); first by auto.
seq 1 0 : (
  #pre /\
  to_list buffer{1} = if leaf_idx{1} `&` W32.one <> W32.zero 
                      then (load_mem_w8_list32 mem auth_path_ptr{1})  ++ to_list leaf{1}
                      else to_list leaf{1} ++ (load_mem_w8_list32 mem auth_path_ptr{1})
).
(** -------------------------------------------------------------------------------------------- **)
if{1}.
    + wp.
      exists * auth_path_ptr{1}; elim * => P.
      call {1} (p_memcpy_ptr_correct P).
      wp.
      exists * leaf{1}; elim * => P0.
      call {1} (_x_memcpy_u8u8_post P0).
      auto => /> &1 *; do split. 
         * admit.
         * admit.
         * admit.
         * move => *.
           apply (eq_from_nth witness).
                - rewrite size_cat !size_to_list size_load_mem_w8_list32 //.
           rewrite size_to_list => j?.
           rewrite get_to_list initiE // => />.
           case (0 <= j < 32) => *.
                - rewrite nth_cat size_load_mem_w8_list32 ifT 1:/# /load_mem_w8_list32 initiE // nth_mkseq //.
                - rewrite nth_cat size_load_mem_w8_list32 ifF 1:/# /load_mem_w8_list32 initiE // nth_mkseq 1:/# => />.
                  by rewrite ifT 1:/#.
    + wp. 
      exists * auth_path_ptr{1}; elim * => P.
      ecall {1} (p_memcpy_ptr_correct P). (* we need the phoare variant of the lemma *)
      wp.
      exists * buffer{1}, leaf{1}; elim * => P0 P1.
      call {1} (_x_memcpy_u8u8_64_32_post P0 P1). (* we need the phoare variant of the lemma *)
      auto => /> &1  ? result H0 H1 *;  do split.
         * admit.
         * admit.
         * admit.
         * move => *.
           apply (eq_from_nth witness).
                - by rewrite size_cat size_load_mem_w8_list32 !size_to_list.
           rewrite size_to_list => j?.
           rewrite nth_cat size_to_list.
           case (0 <= j < 32) => *.
                - rewrite ifT 1:/# get_to_list initiE // -H0 => />.
                  by rewrite ifF 1:/# nth_sub.   
                - rewrite ifF 1:/# get_to_list initiE // => />.
                  rewrite ifT 1:/# initiE 1:/# => />.
                  rewrite /load_mem_w8_list32 nth_mkseq /#.
(** -------------------------------------------------------------------------------------------- **)
seq 1 0 : (
    Glob.mem{1} = mem /\ 
    Glob.mem{2} = mem /\
    auth_path_ptr{1} = _auth_path_ptr{1} + W64.of_int 32 /\ 
    t32{1} = leaf_idx{1} `&` W32.one /\
    to_list buffer{1} =
            if leaf_idx{1} `&` W32.one <> W32.zero 
            then load_mem_w8_list32 mem _auth_path_ptr{1} ++ to_list leaf{1}
            else to_list leaf{1} ++ load_mem_w8_list32 mem _auth_path_ptr{1}
); first by auto.
(** -------------------------------------------------------------------------------------------- **)
(* While loop starts here => the lhs has one iteration less than the rhs *)
admit.
qed.
