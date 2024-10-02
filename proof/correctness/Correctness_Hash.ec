pragma Goals : printall.

require import AllCore List RealExp IntDiv.
from Jasmin require import JModel.

require import XMSS_IMPL Parameters.
require import Params Address Hash.
require import Correctness_Bytes Correctness_Mem Correctness_Address.
require import Utils2.

require import Array8 Array32 Array64 Array96 Array128.

axiom hash_96 (x : W8.t Array96.t) :
  phoare[
      M(Syscall).__core_hash_96 : 
      arg.`2 = x 
      ==>  
      to_list res = val (Hash (to_list x))
    ] = 1%r.

axiom hash_128 (x : W8.t Array128.t) :
  phoare[
      M(Syscall).__core_hash_128 : 
      arg.`2 = x 
      ==> 
      to_list res = val (Hash (to_list x))
    ] = 1%r.

op load_buf (mem : global_mem_t) (ptr : W64.t) (len : int) : W8.t list =
  mkseq (fun i => loadW8 mem (to_uint ptr + i)) len.

axiom hash_ptr_correct (mem : global_mem_t) (ptr len : W64.t) :
  phoare[
      M(Syscall).__core_hash_in_ptr_ :
      valid_ptr_i ptr (to_uint len) /\
      arg.`2 = ptr /\
      arg.`3 = len 
      ==>
      to_list res = val (Hash (load_buf mem ptr (to_uint len)))
  ] = 1%r.


lemma prf_correctness (a b : W8.t Array32.t) :
    n = XMSS_N /\
    prf_padding_val = XMSS_HASH_PADDING_PRF /\ 
    padding_len = XMSS_PADDING_LEN =>
    equiv [
    M(Syscall).__prf ~ Hash.prf : 
    arg{1}.`2 = a /\ 
    arg{1}.`3 = b /\ 
    arg{2} = (NBytes.insubd (to_list a), NBytes.insubd (to_list b)) 
    ==>
    val res{2} = to_list res{1}
    ].
proof.
rewrite /XMSS_N /XMSS_HASH_PADDING_PRF /XMSS_PADDING_LEN => [#] n_val pval plen.
proc.
seq 9 2 : (buf{2} = to_list buf{1}); last first.
  + inline M(Syscall).__core_hash__96 M(Syscall)._core_hash_96; wp; sp.
    ecall {1} (hash_96 buf{1}); auto => /> /#.
seq 3 0 : (#pre); 1:auto. 
seq 1 1 : (#pre /\ padding{2} = to_list padding_buf{1}).
  + call {1} (ull_to_bytes_32_correct (of_int 3)%W64). 
    auto => /> ? ->. 
    by rewrite plen pval.
seq 1 0 : (
  val key{2} = to_list key{1} /\
  val in_0{2} = to_list in_0{1} /\
  padding{2} = to_list padding_buf{1} /\ 
  forall (k : int), 0 <= k < 32 => buf{1}.[k] = nth witness padding{2} k
).
    + auto => /> &1; do split; 1,2: by rewrite insubdK /P //= size_to_list n_val.  
      move => k??.
      rewrite initiE 1:/# => />.  
      by rewrite ifT. 
seq 1 0 : (#pre /\ aux{1} = key{1}); first by ecall {1} (_x_memcpy_u8u8_post key{1}); auto => />.
seq 1 0 : (#pre /\ forall (k : int), 32 <= k < 64 => buf{1}.[k] = nth witness (val key{2}) (k - 32)).
    + auto => /> &1 &2 H0 H1 H2; split => k??.  
         - rewrite initiE 1:/# => />.     
           rewrite ifF 1:/#. 
           apply H2 => //. 
         - rewrite initiE 1:/# => />. 
           rewrite ifT //= H0 get_to_list //=.
seq 1 0 : (
  val key{2} = to_list key{1} /\
  val in_0{2} = to_list in_0{1} /\
  padding{2} = to_list padding_buf{1} /\ 
  (forall (k : int), 0 <= k < 32 => buf{1}.[k] = nth witness padding{2} k) /\
  (forall (k : int), 32 <= k < 64 => buf{1}.[k] = nth witness (val key{2}) (k - 32)) /\
  aux{1} = in_0{1}
); first by ecall {1} (_x_memcpy_u8u8_post in_0{1}); auto => /> /#.
seq 1 0 : (
  val key{2} = to_list key{1} /\
  val in_0{2} = to_list in_0{1} /\ 
  padding{2} = to_list padding_buf{1} /\ 
  size padding{2} = 32 /\
  (forall (k : int), 0 <= k < 32 => buf{1}.[k] = nth witness padding{2} k) /\
  (forall (k : int), 32 <= k < 64 => buf{1}.[k] = nth witness (val key{2}) (k - 32)) /\
  (forall (k : int), 64 <= k < 96 => buf{1}.[k] = nth witness (val in_0{2}) (k - 64))
).
    + auto => /> &1 &2 H0 H1 H2 H3 *.
      do split; first by rewrite size_to_list. 
         - move => k??. 
           rewrite initiE 1:/# => />.
           rewrite ifF 1:/#. 
           apply H2 => //. 
         - move => k??. 
           rewrite initiE 1:/# => />.
           rewrite ifF 1:/#. 
           apply H3 => //. 
         - move => k??. 
           rewrite initiE 1:/# => />.
           rewrite ifT // -get_to_list -H1 //.        
auto => /> &1 &2 H0 H1 H2 H3 H4 H5. 
apply (eq_from_nth witness).
    + rewrite !size_cat !size_to_list !valP n_val //. 
rewrite !size_cat H0 !size_to_list //= valP n_val  //= => i?. 
case (0 <= i < 32).
    + move => ?.
      rewrite nth_cat size_cat !size_to_list ifT 1:/# nth_cat !size_to_list ifT 1:/# get_to_list /#. 
case (32 <= i < 64).
    + move => ?_.
      rewrite nth_cat size_cat !size_to_list ifT 1:/# nth_cat size_to_list ifF 1:/# -H0 /#. 
move => ??.
rewrite nth_cat size_cat !size_to_list ifF 1:/# H5 // /#. 
qed.

lemma prf_keygen_correctness (a : W8.t Array64.t, b : W8.t Array32.t) :
    n = XMSS_N /\
    prf_kg_padding_val = XMSS_HASH_PADDING_PRF_KEYGEN /\ 
    padding_len = XMSS_PADDING_LEN =>
    equiv [
      M(Syscall).__prf_keygen ~ Hash.prf_keygen : 
      arg{1}.`2 = a /\ 
      arg{1}.`3 = b /\ 
      arg{2} = (to_list a, NBytes.insubd (to_list b))
      ==>
      val res{2} = to_list res{1}
    ].
proof.
rewrite /XMSS_N /XMSS_HASH_PADDING_PRF_KEYGEN /XMSS_PADDING_LEN => [#] n_val pval plen.
proc => //=.
seq 9 2 : (buf{2} = to_list buf{1}); last first.
  + inline M(Syscall).__core_hash__128 M(Syscall)._core_hash_128; wp; sp.
    ecall {1} (hash_128 buf{1}); auto => /> /#.
seq 3 0 : (#pre); 1:auto.
seq 1 1 : (#pre /\ padding{2} = to_list padding_buf{1}).
  + call {1} (ull_to_bytes_32_correct (of_int 4)%W64). 
    auto => /> ? ->. 
    by rewrite pval plen.
seq 1 0 : (
  val key{2} = to_list key{1} /\
  in_0{2} = to_list in_0{1} /\
  padding{2} = to_list padding_buf{1} /\ 
  forall (k : int), 0 <= k < 32 => buf{1}.[k] = nth witness padding{2} k
).
    + auto => /> &1; split.
         * rewrite NBytes.insubdK // /P size_to_list n_val //.
         * move => k??.
           rewrite initiE 1:/# => />. 
           by rewrite ifT.
seq 1 0 : (#pre /\ aux{1} = key{1}); first by ecall {1} (_x_memcpy_u8u8_post key{1}); auto => />.
seq 1 0 : (
    #pre /\ 
    forall (k : int), 32 <= k < 64 => buf{1}.[k] = nth witness (val key{2}) (k - 32)
).
    + auto => /> &1 &2 H0 H1; split => k??.
         * rewrite initiE 1:/# => />. 
           rewrite ifF 1:/#.
           apply H1 => //.
         * rewrite initiE 1:/# => />.
           by rewrite ifT 1:/# H0 get_to_list.           
seq 1 0 : (
  val key{2} = to_list key{1} /\
  in_0{2} = to_list in_0{1} /\
  padding{2} = to_list padding_buf{1} /\ 
  (forall (k : int), 0 <= k < 32 => buf{1}.[k] = nth witness padding{2} k) /\
  (forall (k : int), 32 <= k < 64 => buf{1}.[k] = nth witness (val key{2}) (k - 32)) /\
  aux_0{1} = in_0{1}
).
    + ecall {1} (_x_memcpy_u8u8_64_post in_0{1}); auto => /> /#.
seq 1 0 : (
  val key{2} = to_list key{1} /\
  in_0{2} = to_list in_0{1} /\ 
  size in_0{2} = 64 /\
  padding{2} = to_list padding_buf{1} /\
  (forall (k : int), 0 <= k < 32 => buf{1}.[k] = nth witness padding{2} k) /\
  (forall (k : int), 32 <= k < 64 => buf{1}.[k] = nth witness (val key{2}) (k - 32)) /\
  (forall (k : int), 64 <= k < 128 => buf{1}.[k] = nth witness in_0{2} (k - 64))
).
    + auto => /> &1 &2 H0 H1 H2; do split. 
         * by rewrite size_to_list.  
         * move => k??.
           rewrite initiE 1:/# => />.
           rewrite ifF 1:/#.
           apply H1 => //.
         * move => k??.
           rewrite initiE 1:/# => />.
           rewrite ifF 1:/#. 
           apply H2 => //.
         * move => k??.
           rewrite initiE 1:/# => />.
           by rewrite ifT 1:/#. 
auto => /> &1 &2 H0 H1 H2 H3 H4.
apply (eq_from_nth witness). 
    + rewrite !size_cat H0 !size_to_list //=.
rewrite !size_cat H0 !size_to_list //= => i?.
case (0 <= i < 32).
    + move => ?.
      rewrite nth_cat !size_cat !size_to_list //= ifT 1:/#.
      rewrite nth_cat !size_to_list //= ifT /#.
case (32 <= i < 64). 
    + move => ?_.
      rewrite nth_cat !size_cat !size_to_list //= ifT 1:/#.
      rewrite nth_cat !size_to_list //= ifF 1:/#.
      rewrite -!get_to_list -H0 /#.
move => ??.
rewrite nth_cat !size_cat !size_to_list //= ifF /#.
qed.

op merge_nbytes_to_array (a b : nbytes) : W8.t Array64.t = 
  Array64.init (fun i => if 0 <= i < 32 
                         then nth witness (val a) i 
                         else nth witness (val b) (i - 32)).

lemma rand_hash_correct (i0 i1: nbytes, _pub_seed : W8.t Array32.t, _in : W8.t Array64.t, a : W32.t Array8.t) :
    padding_len = XMSS_PADDING_LEN /\ 
    prf_padding_val = XMSS_HASH_PADDING_PRF /\
    padding_len = XMSS_PADDING_LEN /\ 
    n = XMSS_N  =>
    equiv [
      M(Syscall).__thash_h ~ Hash.rand_hash :
      arg{1}.`2 = (merge_nbytes_to_array i0 i1) /\
      arg{1}.`3 = _pub_seed /\
      arg{1}.`4 = a /\
      arg{2} = (i0, i1, NBytes.insubd(to_list _pub_seed), a)
      ==>
      to_list res{1}.`1 = val res{2}
    ].
proof.
rewrite /XMSS_PADDING_LEN /XMSS_HASH_PADDING_PRF /XMSS_PADDING_LEN /XMSS_N => [#] plen pval pprfval nval.
proc.
seq 3 0 : (#pre); 1:auto. 
seq 1 1 : (#pre /\ padding{2} = to_list aux{1} /\ size padding{2} = 32).
    + call {1} (ull_to_bytes_32_correct W64.one). 
      auto => /> ? ->; split => [/# |]. 
      rewrite size_lenbytes_be64 /#.   
swap {1} [2..3] -1.
conseq (: 
  addr{1} = address{2} /\
  to_list in_0{1} = (val _left{2}) ++ (val _right{2}) /\
  val _seed{2} = to_list pub_seed{1} /\ 
  padding{2} = to_list aux{1} /\   
  size padding{2} = 32
  ==> 
  _
).
    + auto => /> &1 ?; split. 
         * apply (eq_from_nth witness). 
             - by rewrite size_to_list size_cat !valP nval.
           rewrite size_to_list => j?. 
           rewrite get_to_list /merge_nbytes_to_array initiE 1:/# => />. 
           case (0 <= j < 32) => ?. 
             - by rewrite nth_cat valP nval ifT 1:/#.
           by rewrite nth_cat valP nval ifF 1:/#. 
         * by rewrite NBytes.insubdK //= /P size_to_list nval.
seq 2 2 : (
  addr{1} = address{2} /\
  to_list in_0{1} = val _left{2} ++ val _right{2} /\
  val _seed{2} = to_list pub_seed{1} /\
  padding{2} = to_list aux{1} /\ 
  size padding{2} = 32 /\

  val addr_bytes{2} = to_list addr_as_bytes{1} 
).
    + inline {1} M(Syscall).__set_key_and_mask.
      ecall {1} (addr_to_bytes_correctness addr{1}).
      auto => /> &1 &2 ??? r ->.
      by rewrite /set_key_and_mask.  
seq 1 0 : (
  #pre /\
  forall (k : int), 0 <= k < 32 => buf{1}.[k] = nth witness padding{2} k
); first by auto => /> *; rewrite initE ifT 1:/#; auto => /> /#.
seq 1 1 : (
  to_list in_0{1} = (val _left{2}) ++ (val _right{2}) /\
  val _seed{2} = to_list pub_seed{1} /\ 
  address{2} = addr{1} /\
  val addr_bytes{2} = to_list addr_as_bytes{1} /\
  size padding{2} = 32 /\
  val key{2} = to_list aux{1} /\
  forall (k : int), 0 <= k < 32 => buf{1}.[k] = nth witness padding{2} k
).
    + inline {1} M(Syscall).__prf_ M(Syscall)._prf; wp; sp.
      exists * in_01{1}, key0{1}; elim * => _P1 _P2.
      call {1} (prf_correctness _P1 _P2) => [/# |].  
      skip => /> &1 &2 ? H0 *.
      rewrite -H0 #smt:(@NBytes).
seq 11 6 : (
  addr{1} = address{2} /\
  to_list buf{1} = padding{2} ++ (val key{2}) ++ bytexor ((val _left{2}) ++ (val _right{2})) ((val bitmask_0{2}) ++ (val bitmask_1{2}))
); last first. 
    + inline {1}  M(Syscall)._core_hash_128. 
      wp. 
      ecall {1} (hash_128 in_00{1}). 
      auto => /> &1 &2 ?_ -> /#.
seq 1 0 : (
    #pre /\
    forall (k : int), 0 <= k < 32 => buf{1}.[32 + k] = nth witness (val key{2}) k
).
    + auto => /> &1 &2 ???? H *; split => k??; rewrite initiE 1:/# => />.
         * rewrite ifF /#.                       
         * by rewrite ifT 1:/# H get_to_list.
seq 2 2 : (
  to_list in_0{1} = val _left{2} ++ val _right{2} /\
  val _seed{2} = to_list pub_seed{1} /\
  address{2} = addr{1} /\
  val addr_bytes{2} = to_list addr_as_bytes{1} /\
  size padding{2} = 32 /\
  val key{2} = to_list aux{1} /\
  (forall (k : int), 0 <= k < 32 => buf{1}.[k] = nth witness padding{2} k) /\
  (forall (k : int), 0 <= k < 32 => buf{1}.[32 + k] = nth witness (val key{2}) k)
).
    + inline {1} M(Syscall).__set_key_and_mask.
      ecall {1} (addr_to_bytes_correctness addr{1}); auto => /> /#.
seq 2 1 : (
  to_list in_0{1} = val _left{2} ++ val _right{2} /\
  val _seed{2} = to_list pub_seed{1} /\ 
  address{2} = addr{1} /\
  val addr_bytes{2} = to_list addr_as_bytes{1} /\
  size padding{2} = 32 /\
  (forall (k : int), 0 <= k < 32 => bitmask{1}.[k] = nth witness (val bitmask_0{2}) k) /\
  (forall (k : int), 0 <= k < 32 => buf{1}.[k] = nth witness padding{2} k) /\
  (forall (k : int), 0 <= k < 32 => buf{1}.[32 + k] = nth witness (val key{2}) k)
).
    + inline {1} M(Syscall).__prf_ M(Syscall)._prf; wp; sp.
      exists * in_01{1}, key0{1}; elim * => _P1 _P2; call {1} (prf_correctness _P1 _P2) => [/# |]. 
      skip => /> &1 &2 ? H*. 
      split; [rewrite -H #smt:(@NBytes) |]. 
      move => ???? H0 ???. 
      rewrite initE ifT 1:/# => />.
      by rewrite ifT //= H0 get_to_list.
seq 2 2 : (
  to_list in_0{1} = val _left{2} ++ val _right{2} /\
  val _seed{2} = to_list pub_seed{1} /\
  address{2} = addr{1} /\
  val addr_bytes{2} = to_list addr_as_bytes{1} /\
  size padding{2} = 32 /\
  (forall (k : int), 0 <= k < 32 => bitmask{1}.[k] = nth witness (val bitmask_0{2}) k) /\
  (forall (k : int), 0 <= k < 32 => buf{1}.[k] = nth witness padding{2} k) /\
  (forall (k : int), 0 <= k < 32 => buf{1}.[32 + k] = nth witness (val key{2}) k)
).
    + inline {1} M(Syscall).__set_key_and_mask.
      ecall {1} (addr_to_bytes_correctness addr{1}); auto => /> /#.
seq 2 1 : (
  #pre /\ 
  (forall (k : int), 0 <= k < 32 => bitmask{1}.[32 + k] = nth witness (val bitmask_1{2}) k)
). 
    + inline {1} M(Syscall).__prf_ M(Syscall)._prf; wp; sp.
      exists * in_01{1}, key0{1}; elim * => _P1 _P2; call {1} (prf_correctness _P1 _P2) => [/# |].
      skip => /> &1 &2 ?H H0 H1 H2 H3 H4.
      do split => [| | H5 H6 rL rR H7]. 
         * rewrite -H0 #smt:(@NBytes). 
         * rewrite -H #smt:(@NBytes). 
         * split => k??; rewrite initiE 1:/# => />.
              - rewrite ifF 1:/#. 
                by apply H2.
              - by rewrite ifT 1:/# H7 get_to_list. 
conseq (: _ ==>
  size padding{2} = 32 /\
  addr{1} = address{2} /\ 
  (forall (k : int), 0 <= k < 32 => buf{1}.[k] = nth witness padding{2} k) /\
  (forall (k : int), 0 <= k < 32 => buf{1}.[32 + k] = nth witness (val key{2}) k) /\
  (forall (k : int), 0 <= k < 64 => buf{1}.[64 + k] = nth witness (bytexor (val _left{2} ++ val _right{2}) (val bitmask_0{2} ++ val bitmask_1{2})) k)
).
    + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 bufL H8 H9 H10. 
      apply (eq_from_nth witness). 
        * rewrite !size_cat H3 /bytexor !size_map size_zip !size_cat !valP size_iota nval //=.
      rewrite size_to_list => i?.
      rewrite get_to_list.
      case (0 <= i < 32); first by smt(@List @Array128).
      case (32 <= i < 64).
        * move => ? _. 
          rewrite nth_cat.
          have ->: size (padding{2} ++ val key{2}) = 64 by smt(size_cat NBytes.valP).
          rewrite ifT 1:/# nth_cat ifF /#. 
      move => Ht0 Ht1. 
      have H: 64 <= i < 128 by smt(). 
      rewrite nth_cat.
      have ->: size (padding{2} ++ val key{2}) = 64 by smt(size_cat NBytes.valP).
      rewrite ifF /#.
while {1} ( 
  0 <= to_uint i{1} <= 64 /\
  size padding{2} = 32 /\ 
  addr{1} = address{2} /\
  to_list in_0{1} = val _left{2} ++ val _right{2} /\
  to_list bitmask{1} = val bitmask_0{2} ++ val bitmask_1{2} /\
  (forall (k : int), 0 <= k < 32 => buf{1}.[k] = nth witness padding{2} k) /\
  (forall (k : int), 0 <= k < 32 => buf{1}.[32 + k] = nth witness (val key{2}) k) /\
  (forall (k : int), 0 <= k < to_uint i{1} => 
    buf{1}.[64 + k] = 
      nth witness (val _left{2} ++ val _right{2}) (k) `^` nth witness (val bitmask_0{2} ++ val bitmask_1{2}) (k))
) (64 - to_uint i{1}).
    + auto => /> &hr ?? H0 H1 H2 H3 H4 H5 H6.
      have T: 0 <= to_uint i{hr} < 64 by smt(@W64). 
      do split;1,2,6:smt(@W64 pow2_64).      
       * move => k??.   
         rewrite get_setE 1:#smt:(@W64) ifF 1:#smt:(@W64 pow2_64) /#.       
       * move => k??.   
         rewrite get_setE 1:#smt:(@W64) ifF 1:#smt:(@W64 pow2_64) /#.
       * move => k?. 
         rewrite to_uintD_small 1:#smt:(@W64) (: to_uint W64.one = 1) 1:/# => ?.  
         have E0: forall (k : int), 0 <= k < 32 => in_0{hr}.[k] = nth witness (val _left{m}) k by smt(@List @Array64 @NBytes). 
         have E1: forall (k : int), 0 <= k < 32 => in_0{hr}.[32 + k] = nth witness (val _right{m}) k by smt(@List @Array64 @NBytes). 
         have E2: forall (k : int), 0 <= k < 32 => bitmask{hr}.[k] = nth witness (val bitmask_0{m}) k by smt(@List @Array64 @NBytes). 
         have E3: forall (k : int), 0 <= k < 32 => bitmask{hr}.[32 + k] = nth witness (val bitmask_1{m}) k by smt(@List @Array64 @NBytes).
         rewrite get_setE 1:#smt:(@W64).
         rewrite to_uintD_small 1:#smt:(@W64) of_uintK //=. 
         case (64 + k = 64 + to_uint i{hr}) => *; last by apply H5; smt(@W64 pow2_64).
         rewrite nth_cat valP nval.
         have ->: to_uint i{hr} = k by smt(@W64 pow2_64).
         congr; [smt(@List @Array64) |].        
         rewrite nth_cat valP /#.
    + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7.
      do split; 2:smt().
        * apply (eq_from_nth witness). 
             - by rewrite size_to_list size_cat !valP nval. 
          rewrite size_to_list => j?.
          rewrite get_to_list. 
          case (0 <= j < 32) => ?.        
             - rewrite nth_cat valP nval ifT /#.
             - rewrite nth_cat valP nval ifF /#.
        * move => bufL iL; do split.
             - move => *; smt(@W64).
             - move => Ht0 Ht1 Ht2 H11 H12 H13 H14. 
               move => k Hk0 Hk1. 
               rewrite /bytexor (nth_map witness); [by rewrite size_zip !size_cat !valP /# |].            
               auto => />.
               have ->: (nth witness (zip (val _left{2} ++ val _right{2}) (val bitmask_0{2} ++ val bitmask_1{2})) k).`1 = nth witness (val _left{2} ++ val _right{2}) k by smt(@List @NBytes). 
               have ->: (nth witness (zip (val _left{2} ++ val _right{2}) (val bitmask_0{2} ++ val bitmask_1{2})) k).`2 = nth witness (val bitmask_0{2} ++ val bitmask_1{2}) k by smt(@List @NBytes). 
               apply H14.
               smt(@W64 pow2_64).
qed.

lemma hash_message_correct (mem : global_mem_t) (R _root : W8.t Array32.t) (_idx msg_ptr _mlen : W64.t) :
    hoare [
      M(Syscall).__hash_message :

      valid_ptr msg_ptr _mlen /\
      0 < to_uint _mlen /\

      arg.`2 = R /\
      arg.`3 = _root /\
      arg.`4 = _idx /\
      arg.`5 = msg_ptr /\
      arg.`6 = mlen /\
      Glob.mem = mem
      ==>
      false
    ].
proof.
proc => /=.
seq 2 : #pre; first by auto.
seq 1 : (#pre /\ to_list buf = lenbytes_be64 (of_int 2)%W64 32).
  + (* call {1} (ull_to_bytes_32_correct ((of_int 2)%W64)) doesnt work *)
    admit.

seq 9 : (
  valid_ptr_i m_with_prefix_ptr (to_uint len + 128) /\
  load_buf Glob.mem m_with_prefix_ptr (to_uint len + 128) = 
  (lenbytes_be64 (of_int 2)%W64 32) ++ to_list r ++ to_list root ++ (lenbytes_be64 idx 32) ++ load_buf Glob.mem m_with_prefix_ptr (to_uint len)
); first by admit.

seq 2 : (#pre /\ to_uint len = to_uint mlen + 128).
    + auto => /> &hr.  
      rewrite /valid_ptr_i => [#] *.
      split.

        * admit.
        * rewrite to_uintD_small. 
            - admit.
          by rewrite of_uintK /=.
admit.
qed.
