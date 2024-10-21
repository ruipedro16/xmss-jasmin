pragma Goals : printall.

require import AllCore List Distr RealExp IntDiv.

from Jasmin require import JModel.

require import BitEncoding.
(*---*) import BitChunking.
(*---*) import StdBigop.Bigint.
(*---*) import W4u8.Pack.

require import Array4 Array8 Array32.
require import WArray4.

require import Params Address Repr2 Utils2.
require import XMSS_IMPL.

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

lemma u32_to_bytes_correct (x : W32.t) :
    hoare [M(Syscall).__u32_to_bytes : arg.`2 = x ==> to_list res = W32toBytes x].
proof.
proc.
auto => /> &hr.
rewrite /W32toBytes.
apply (eq_from_nth witness).
  + rewrite size_to_list size_map size_chunk //. 
rewrite size_to_list => i?. 
rewrite get_to_list initiE // (nth_map witness).
  + rewrite size_chunk //. 
rewrite /BSWAP_32 => />.
rewrite ifT // /chunk nth_mkseq /(\bits8) => />.
rewrite wordP => j?.
rewrite initiE // /(\o) /= /bits2w => />.
rewrite initiE // nth_take // 1:/# nth_drop 1,2:/# /w2bits nth_mkseq 1:/# /= /unpack8 /=.
rewrite pack4E initiE 1:/# //= /(\bits8).
rewrite get_of_list 1:/# /= nth_rev.
  + rewrite size_to_list /#.
rewrite size_to_list => />.
rewrite initiE 1:/# /= initiE 1:/# /=.
congr.
(* Isto e verdade ?? *)
admit.
qed.

lemma _addr_to_bytes_correctness (x : W32.t Array8.t) : 
    n = 32 =>
    hoare[M(Syscall).__addr_to_bytes : 
        arg.`2 = x ==> to_list res = val (addr_to_bytes x)].
proof.
move => n_val.
proc.
while (
  #pre /\
  0 <= i <= 8 /\
  forall (k : int), 0 <= k < 4*i => addr_as_bytes.[k] = nth witness (val (addr_to_bytes x)) k
).
    + seq 2 : (#pre /\ to_list buf = W32toBytes addr.[i]).
         * ecall (u32_to_bytes_correct addr.[i]); auto => />. 
      auto => /> &hr H0 H1 H2 H3 H4. 
      do split; 1,2: by smt(). 
      move => k??.
      rewrite initiE 1:/# => />. 
      case (4 * i{hr} <= k < 4 * i{hr} + 4) => *.
         * rewrite -get_to_list H4 /W32toBytes /addr_to_bytes.
           rewrite (nth_map witness); [rewrite size_chunk // size_w2bits /# |] => />.
           rewrite insubdK.  
              - rewrite /P /BitsToBytes size_map size_chunk // size_flatten sumzE BIA.big_map /(\o) //=. 
                rewrite -(StdBigop.Bigint.BIA.eq_big_seq (fun _ => 32)) /=. 
                      + admit.
                rewrite big_constz count_predT size_mkseq n_val /#.
           rewrite /BitsToBytes. 
           rewrite (nth_map witness); [rewrite size_iota size_w2bits /# |].
           rewrite size_w2bits nth_iota 1:/# => />.
           rewrite wordP => j?.
           rewrite (nth_map witness). 
              - rewrite size_chunk // size_flatten sumzE BIA.big_map /(\o) //=. 
                rewrite -(StdBigop.Bigint.BIA.eq_big_seq (fun _ => 32)).
                      + admit.
                rewrite big_constz count_predT size_mkseq /#.
           rewrite /chunk nth_mkseq => />.
              - admit.
           rewrite /w2bits.
           admit.
         * rewrite H2 // /#.
    + auto => /> &hr.
      split => [/# |].
      move => addBytes j ???.
      have ->: j = 8 by smt(). 
      move => H.
      apply (eq_from_nth witness).
         * rewrite size_to_list valP n_val //.
      rewrite size_to_list => k?. 
      rewrite get_to_list H //. 
qed.

lemma addr_to_bytes_ll : islossless M(Syscall).__addr_to_bytes by proc; inline; while (true) (8 - i); auto => /> /#.

lemma addr_to_bytes_correctness (x : W32.t Array8.t) : 
    phoare[M(Syscall).__addr_to_bytes : arg.`2 = x ==> 
      to_list res = val (addr_to_bytes x)] = 1%r.
proof.
proc.
admit.
qed.
