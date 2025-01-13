pragma Goals : printall.

require import AllCore List RealExp IntDiv.

from Jasmin require import JModel JArray.

require import Params Address Hash BaseW WOTS. 

require import XMSS_IMPL Parameters.

require import Array2 Array3 Array8 Array32 Array64 Array67 Array96 Array2144.

require import WArray32.

require import Correctness_Bytes Correctness_Mem Correctness_Address Correctness_Hash. 
require import Repr.
require import Utils.

lemma zip_fst (a b : W8.t list) (i : int):
  0 <= i < min (size a) (size b) =>
    (nth witness (zip a b) i).`1 = nth witness a i 
      by smt(@List).

lemma zip_snd (a b : W8.t list) (i : int):
  0 <= i < min (size a) (size b) =>
    (nth witness (zip a b) i).`2 = nth witness b i 
      by smt(@List).

module ThashF = {
  proc thash_f (t : nbytes, seed : seed, address : adrs) : (nbytes * adrs) = {
    var key : nbytes;
    var bitmask : nbytes;
    var addr_bytes : nbytes;
    
    addr_bytes <- addr_to_bytes address;
    key <@ Hash.prf(addr_bytes, seed);
    address <- set_key_and_mask address 1;
    addr_bytes <- addr_to_bytes address;
    bitmask <@ Hash.prf(addr_bytes, seed);
    t <@ Hash._F(key, nbytexor t bitmask);
    return (t, address);
  }
}.

lemma thash_f_equiv (_out_ _seed_ : W8.t Array32.t) (a : W32.t Array8.t) :
    n = XMSS_N /\
    prf_padding_val = XMSS_HASH_PADDING_PRF /\
    padding_len = XMSS_PADDING_LEN /\ 
    F_padding_val = XMSS_HASH_PADDING_F =>
    equiv [
      M(Syscall).__thash_f ~ ThashF.thash_f :
      arg{1}.`1 = _out_ /\
      arg{1}.`2 = _seed_ /\
      arg{1}.`3 = a /\
      
      arg{2}.`1 = NBytes.insubd (to_list _out_) /\
      arg{2}.`2 = NBytes.insubd (to_list _seed_) /\
      arg{2}.`3 = a
      ==>
      to_list res{1}.`1 = val res{2}.`1 /\
      res{1}.`2 = res{2}.`2 /\
      res{1}.`2.[7] = W32.one /\
      sub res{1}.`2 0 7 = sub a 0 7
    ].
proof. 
rewrite /XMSS_N. 
move => [#] n_val ???.
proc => /=.
seq 4 0 : #pre; first by auto.

seq 1 1 : (#pre /\ to_list addr_as_bytes{1} = val addr_bytes{2}).
  + by ecall {1} (addr_to_bytes_correctness addr{1}); auto.

inline {2} Hash._F. 

swap {2} 7 -6.

seq 2 1 : (#pre /\ to_list padding{1} = padding{2}).
  + auto.
    ecall {1} (ull_to_bytes_32_correct W64.zero).
    auto => /> &1 &2 ??->. 
    congr => /#.

seq 1 0 : (#pre /\ sub buf{1} 0 n = padding{2}).
  + auto => /> &1 &2 ?.
    apply (eq_from_nth witness); first by rewrite size_to_list n_val size_sub.
    rewrite n_val size_sub // => j?.
    by rewrite get_to_list nth_sub // initiE 1:/# /= ifT.

seq 1 1 : (#pre /\ to_list aux{1} = val key{2}).
  + inline {1} M(Syscall).__prf_ M(Syscall)._prf; wp; sp.
    exists * in_00{1}, key0{1}; elim * => _P1 _P2.
    call {1} (prf_correctness _P1 _P2) => [/# |]. 
    skip => /> &1 &2 H0 H1.
    split; [smt(@NBytes) | smt()].

seq 1 0 : (#pre /\ sub buf{1} n n = val key{2}).
  + auto => /> &1 &2 H0 H1 H2. 
    split.
      - apply (eq_from_nth witness); first by rewrite n_val size_to_list size_sub.
        rewrite n_val size_sub // => j?.
        by rewrite -H1 nth_sub //= initiE 1:/# /= ifF 1:/# nth_sub // n_val .
      - apply (eq_from_nth witness); first by rewrite valP n_val size_sub.
        rewrite n_val size_sub // => j?.
        by rewrite nth_sub // initiE 1:/# /= ifT 1:/# -get_to_list H2. 

seq 1 1 : (
  #{/~addr{1} = a}{/~address{2} = a}pre /\ 
  addr{1} = address{2} /\ 
  addr{1}.[7] = W32.one /\
  sub addr{1} 0 7 = sub a 0 7
).
  + inline {1}; auto => /> &1 &2 H0 H1 H2 H3*.
    apply (eq_from_nth witness); first by rewrite !size_sub.
    rewrite size_sub // => j?.
    by rewrite !nth_sub //= get_setE //= ifF 1:/#.

seq 1 1 : (#pre /\ to_list addr_as_bytes{1} = val addr_bytes{2}).
  + by ecall {1} (addr_to_bytes_correctness addr{1}); auto. 

seq 1 1 : (#pre /\ to_list bitmask{1} = val bitmask{2}).
  + inline {1} M(Syscall).__prf_ M(Syscall)._prf; wp; sp.
    exists * in_00{1}, key0{1}; elim * => _P1 _P2.
    call {1} (prf_correctness _P1 _P2) => [/# |]. 
    skip => /> &1 &2 H0 H1 H2 H3 H4 *. 
    split; [smt(@NBytes) | smt()]. 

seq 2 3 : (
  addr{1} = address{2} /\
  addr{1}.[7] = W32.one /\
  sub addr{1} 0 7 = sub a 0 7 /\
  to_list buf{1} = buf{2}
); last first.
  + auto.
    inline {1} M(Syscall).__core_hash__96 M(Syscall)._core_hash_96.
    by wp; sp; ecall {1} (hash_96 in_00{1}); auto => />. 

wp; sp.
 
while {1} 
(
  addr{1} = address{2} /\ 
  addr{1}.[7] = W32.one /\
  sub addr{1} 0 7 = sub a 0 7 /\
  0 <= to_uint i{1} <= 32 /\
  to_list bitmask{1} = val bitmask{2} /\
  to_list out{1} = val t{2} /\
  sub buf{1} 0 n = padding{2} /\
  sub buf{1} n n = val key{2} /\
  sub buf{1} (n + n) (to_uint i{1}) = sub_list (val (nbytexor t{2} bitmask{2})) 0 (to_uint i{1}) 
)
(32 - to_uint i{1}); last first.
  + auto => /> &1 &2 H0 H1 H2 H3 H4 H5 *.
    do split. 
      - by rewrite  insubdK // /P size_to_list n_val.
      - apply (eq_from_nth witness); first by rewrite size_sub_list // size_sub.
        rewrite size_sub // => j? /#.
      - move => bufL iL.
        split => [* |]; first by rewrite ultE /#.
        rewrite ultE of_uintK n_val /= => ??? H6 H7 H8 H9 *.
        apply (eq_from_nth witness); first by by rewrite !size_cat !size_to_list !valP n_val.
        rewrite size_to_list => j?.
        case (0 <= j < 32) => ?.
           + rewrite get_to_list.
             have ->: bufL.[j] = nth witness (sub bufL 0 32) j by rewrite nth_sub.
             by rewrite H6 !nth_cat !size_cat !size_to_list !valP n_val /= ifT 1:/# ifT 1:/# H7 get_to_list.
        case (32 <= j < 64) => ?.
           + rewrite get_to_list.
             have ->: bufL.[j] = nth witness (sub bufL 32 32) (j - 32) by rewrite nth_sub /#.
             by rewrite H8 !nth_cat !size_cat !size_to_list !valP n_val /= ifT 1:/# ifF 1:/#.
        rewrite get_to_list.
        have ->: bufL.[j] = nth witness (sub bufL 64 (to_uint iL)) (j - 64) by rewrite nth_sub /#.
        rewrite H9 !nth_cat !size_cat !size_to_list !valP n_val /= ifF 1:/#.
        by rewrite /sub_list nth_mkseq 1:/#.

auto => /> &hr H0 H1 H2 H3 H4 H5 H6 H7 H8 *.
do split; 1,2,6: by smt(@W64 pow2_64).
  - apply (eq_from_nth witness); first by rewrite !size_sub /#.
    rewrite size_sub 1:/# => j?.        
    rewrite !nth_sub //= get_setE; first by smt(@W64 pow2_64).
    rewrite ifF // to_uintD of_uintK /=/#.
  - apply (eq_from_nth witness); first by rewrite valP size_sub /#.
    rewrite size_sub 1:/# => j?.        
    rewrite !nth_sub //= get_setE; first by smt(@W64 pow2_64).
    rewrite ifF; first by rewrite to_uintD of_uintK /=/#.
    rewrite -H6 n_val /= nth_sub /#.
  - apply (eq_from_nth witness); first by rewrite size_sub to_uintD_small 1..3:/# size_sub_list /#.
    rewrite size_sub to_uintD_small 1..3:/# => j?.
    rewrite nth_sub // /sub_list nth_mkseq // /= get_setE; first by smt(@W64 pow2_64).
    case (to_uint i{hr} = j) => H; [rewrite ifT; first by smt(@W64 pow2_64) | rewrite ifF; first by smt(@W64 pow2_64)]; last first.
        + rewrite n_val /=.
          have ->: buf{hr}.[64 + j] = nth witness (sub buf{hr} (n + n) (to_uint i{hr})) j by rewrite nth_sub 2:/#; smt(@W64 pow2_64).
          rewrite H7 /sub_list nth_mkseq 2:/#; smt(@W64 pow2_64).
        + rewrite /nbytexor insubdK /bytexor; first by rewrite /P size_map size_zip !valP.
          rewrite (nth_map witness) /=. 
             - rewrite size_zip !valP n_val (: min 32 32 = 32) 1:/#; smt(@W64 pow2_64).
               rewrite zip_fst; first by rewrite !valP n_val /=; smt(@W64 pow2_64).
               rewrite zip_snd; first by rewrite !valP n_val /=; smt(@W64 pow2_64).
               rewrite -H4 -!get_to_list H; congr. (* this gets rid of the rhs *)
               congr.               
qed.

lemma gen_chain_correct (_buf_ : W8.t Array32.t, _start_ _steps_ : W32.t, _pub_seed_ : W8.t Array32.t) (a1 a2 : W32.t Array8.t):
    n = XMSS_N /\
    w = XMSS_WOTS_W /\ 
    len = XMSS_WOTS_LEN /\
    prf_padding_val = XMSS_HASH_PADDING_PRF /\ 
    padding_len = XMSS_PADDING_LEN /\ 
    F_padding_val = XMSS_HASH_PADDING_F =>
    equiv [
      M(Syscall).__gen_chain_inplace ~ Chain.chain : 
      arg{1} = (_buf_, _start_, _steps_, _pub_seed_, a1) /\
      arg{2} = (NBytes.insubd (to_list _buf_), to_uint _start_, to_uint _steps_, NBytes.insubd (to_list _pub_seed_), a2) /\
      0 <= to_uint _start_ <= XMSS_WOTS_W - 1/\
      0 <= to_uint _steps_ <= XMSS_WOTS_W - 1 /\
      0 <= to_uint (_start_ + _steps_) <= w - 1 /\
      sub a1 0 6 = sub a2 0 6
      ==> 
      val res{2} = to_list res{1}.`1 /\
      sub res{1}.`2 0 6 = sub a1 0 6 
    ].
proof.
rewrite /XMSS_N /XMSS_WOTS_W => [#] n_val w_val *.
proc => //=.

swap {1} 1 2.

seq 2 1 : ( 
  0 <= to_uint start{1} <= w - 1/\
  0 <= to_uint steps{1} <= w - 1 /\
  0 <= to_uint (start{1} + steps{1}) <= w - 1 /\
  val t{2} = to_list out{1} /\
  i{2} = to_uint start{1} /\
  s{2} = to_uint steps{1} /\
  val _seed{2} = to_list pub_seed{1} /\
  val t{2} = to_list out{1} /\  
  t{1} = start{1} + steps{1} /\
  sub addr{1} 0 6 = sub address{2} 0 6 /\ 
  sub addr{1} 0 6 = sub a1 0 6 /\
  start{1} = _start_ /\
  steps{1} = _steps_ 
); first by auto => /> *; do split => [/# | /# | | |]; by rewrite insubdK /P // size_to_list n_val.

while (
  sub addr{1} 0 6 = sub address{2} 0 6 /\ 
  sub addr{1} 0 6 = sub a1 0 6 /\

  0 <= to_uint start{1} <= w - 1/\
  0 <= to_uint steps{1} <= w - 1 /\ 
  0 <= to_uint (start{1} + steps{1}) <= w - 1 /\

  val t{2} = to_list out{1} /\
  val _seed{2} = to_list pub_seed{1} /\
  
  0 <= chain_count{2} <= s{2} /\
  s{2} = to_uint steps{1} /\ 
  i{2} = to_uint start{1} /\
  to_uint i{1} = i{2} + chain_count{2} /\
  t{1} = start{1} + steps{1} 
); last by auto => /> ; smt(@W32 pow2_32).

seq 2 2 : (#pre /\ address{2} = addr{1}).
    + inline {1}; auto => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 *.
      rewrite /set_key_and_mask /set_hash_addr.
      do split.
         * apply (eq_from_nth witness); first by rewrite !size_sub.
           rewrite size_sub // => j?.
           rewrite !nth_sub // !get_setE // !ifF 1..4:/#.
           smt(sub_k).
         * apply (eq_from_nth witness); first by rewrite !size_sub.
           rewrite size_sub // => j?.
           rewrite !nth_sub // !get_setE // !ifF 1,2:/#.
           smt(sub_k).
         * rewrite tP => j?.
           rewrite !get_setE //.
           case (j = 7) => //?.
           case (j = 6) => //?; first by rewrite -H12 to_uintK.
           smt(sub_k).

outline {2} [1-6] { (t, address) <@ ThashF.thash_f (t, _seed, address); }.

inline {1}  M(Syscall).__thash_f_  M(Syscall)._thash_f.

sp; wp.

conseq />.

exists * out1{1}, pub_seed1{1}, addr1{1}.
elim * => P0 P1 P2.
call (thash_f_equiv P0 P1 P2) => [/# |]. 
skip => /> &1 &2 H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13.
do split; 1,2: by smt(@NBytes).
move => H14 H15 resultL resultR H16 H17 H18 H19.
do split; 1,3..5: by smt().
- smt(sub_N).
- smt(@W32 pow2_32).
- rewrite ultE to_uintD_small 1:/# /= H11 => ?; smt(@W32 pow2_32).
- rewrite ultE to_uintD_small 1:/# /= H11 => ?; smt(@W32 pow2_32).
qed.

