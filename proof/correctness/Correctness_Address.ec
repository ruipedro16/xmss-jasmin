pragma Goals : printall.

require import AllCore List Distr RealExp IntDiv.

from Jasmin require import JModel.

require import BitEncoding.
(*---*) import BitChunking.
(*---*) import StdBigop.Bigint.
(*---*) import W4u8.Pack.

require import Array4 Array8 Array32.
require import WArray4.

require import Params Address Repr2 Utils2 Bytes.
require import XMSS_IMPL.

lemma in_nth ['a] (x : 'a list) (P : 'a -> bool) :
    (forall (x0 : 'a ), x0 \in x => P x0) <=>
    forall (k : int), 0 <= k < size x => P (nth witness x k).
proof.
split ; smt(@List). (* Without the split, smt doesnt work *)
qed.


lemma zero_addr_op_impl (address : adrs) :
    hoare[M(Syscall)._zero_address : true ==> res = zero_addr].
proof.
proc.
while (
  0 <= i <= 8 /\ 
  (forall (k : int), 0 <= k < i => (addr.[k] = W32.zero))
).
    + auto => /> &hr *; do split;1,2:smt().
      move => k??. 
      rewrite get_setE //= /#.
    + auto => /> &hr *; split => [/# |].
      move => addr0 i0 ???. 
      have ->: i0 = 8 by smt(). 
      move => H.
      rewrite /zero_addr tP => j?. 
      rewrite initiE //=.
      apply H => //.
qed.

lemma zero_addr_ll : islossless M(Syscall)._zero_address by proc; while (true) (8 - i); auto => /> /#.

lemma zero_addr_res (address : adrs) :
    phoare[M(Syscall)._zero_address : true ==> res = zero_addr] = 1%r
      by conseq zero_addr_ll (zero_addr_op_impl address) => //=. 

op addrToBytes (a : adrs) : W8.t list = flatten (map W32toBytes (to_list a)).


lemma u32_to_bytes_correct (x : W32.t) :
    phoare [
      M(Syscall).__u32_to_bytes : 
      arg.`2 = x 
      ==>  
      to_list res = W32toBytes x
    ] = 1%r.
proof.
proc.
auto => /> &hr.
apply (eq_from_nth witness).
  + by rewrite size_to_list size_rev size_to_list.
rewrite size_to_list // => i?.
rewrite !get_to_list initiE //.
rewrite /get8 /set32_direct initiE //= ifT 1:/# bits8E /=.
rewrite wordP => j?.
rewrite initiE //= /BSWAP_32 /(\o) pack4E initiE 1:/# /= get_of_list 1:/#.
rewrite nth_rev.
  + rewrite size_to_list /#.
congr => [| /#].
rewrite !get_to_list !size_to_list.
rewrite nth_rev.
  + rewrite size_to_list /#.
rewrite size_to_list.
rewrite /to_list nth_mkseq 1:/# /=.
congr => /#.
qed.

lemma addr_to_bytes_correctness (x : W32.t Array8.t) : 
    n = 32 =>
    phoare[
        M(Syscall).__addr_to_bytes : 
        arg.`2 = x 
        ==> 
        to_list res = flatten (map W32toBytes (to_list x))
] = 1%r.
proof.
move => n_val.
proc.
while ( 
  addr = x /\
  0 <= i <= 8 /\
  sub addr_as_bytes 0 (4 * i) = 
  sub_list (flatten (map W32toBytes (to_list x))) 0 (4 * i)
)
(8 - i); last first.
  + auto => /> *; split.
      - apply (eq_from_nth witness); first by rewrite size_sub // size_sub_list /#.
        rewrite size_sub // /#.
      - move => addrBytes i; split => [/# |].
        move => ???; have ->: i = 8 by smt(). 
        move => /= H.
        apply (eq_from_nth witness).
            * rewrite size_to_list size_flatten.
              rewrite sumzE BIA.big_map /(\o) //=.
              rewrite -(StdBigop.Bigint.BIA.eq_big_seq (fun _ => 4)) /=; last first.
                +  rewrite big_constz count_predT size_map size_to_list /#.
                   rewrite in_nth.
                   rewrite size_map size_to_list /= => j?.
                   rewrite (nth_map witness); first by rewrite size_to_list /#.
                   rewrite /W32toBytes size_rev; first by rewrite size_to_list /#.
        rewrite size_to_list => j?.
        rewrite get_to_list. 
        have ->: addrBytes.[j] =nth witness (sub addrBytes 0 32) j by rewrite nth_sub /#.
        by rewrite H nth_sub_list.

  + auto => />. 
    exists * addr.[i]; elim * => P.
    call (u32_to_bytes_correct P).
    auto => /> &hr H0 H1 H2 H3 result Hr *; do split; 1,2,4: by smt().
    apply (eq_from_nth witness); first by rewrite size_sub_list 1:/# size_sub 1,2:/#.
    rewrite size_sub 1:/# => j?.
    rewrite nth_sub_list 1:/# (nth_flatten witness 4).
       + pose X := (fun (s : W8.t list) => size s = 4).
         pose Y := (map W32toBytes (to_list x)).
         rewrite -(all_nthP X Y witness) /X /Y size_map => k?. 
         by rewrite (nth_map witness) // /W32toBytes size_rev size_to_list.
    rewrite nth_sub 1:/# initiE 1:/# /=.   
    rewrite (nth_map witness); first by rewrite size_to_list /#.
    rewrite /W32toBytes nth_rev; first by rewrite size_to_list /#.
    rewrite get_to_list size_to_list /to_list nth_mkseq 1:/# /=.
    case (4 * i{hr} <= j < 4 * i{hr} + 4) => ?.
       + rewrite (: result.[j - 4 * i{hr}] = nth witness (to_list result) (j - 4 * i{hr})) 1:/# Hr /W32toBytes.
         rewrite nth_rev; first by rewrite size_to_list /#.
         rewrite size_to_list /to_list nth_mkseq 1:/# /= /#.  
       + have ->: addr_as_bytes{hr}.[j] = nth witness (sub addr_as_bytes{hr} 0 (4 * i{hr})) j by rewrite nth_sub /#.
         rewrite H2 nth_sub_list 1:/# (nth_flatten witness 4).
           * pose X := (fun (s : W8.t list) => size s = 4).
             pose Y := (map W32toBytes (to_list x)).
             rewrite -(all_nthP X Y witness) /X /Y size_map => k?. 
             by rewrite (nth_map witness) // /W32toBytes size_rev size_to_list.
         rewrite (nth_map witness); first by rewrite size_to_list /#.
         rewrite /W32toBytes nth_rev; first by rewrite size_to_list /#.
         by rewrite get_to_list size_to_list /to_list nth_mkseq 1:/# /=.
qed.
