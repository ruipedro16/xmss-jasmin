pragma Goals : printall.

require import AllCore List RealExp IntDiv.
from Jasmin require import JModel JArray.

require import Types Params Parameters Address Notation Primitives Hash Wots Util.
require import XMSS_IMPL.

require import Array2 Array3 Array8 Array32 Array64 Array67 Array96 Array2144.

require import Utils. (* valid ptr predicate & addr_to_bytes *)
require import Correctness_Mem Correctness_Hash. 
(*---*) import NBytes.

require import Termination Repr.

require import BitEncoding.
(*---*) import BitChunking.

lemma size_prf : hoare[Hash.prf : true ==> size res = n]
    by proc; seq 2 : (#pre); auto => />; smt(size_hash).

lemma size_F : hoare[Hash._F : true ==> size res = n]
    by proc; seq 2: (true); auto => />; smt(size_hash). 

lemma size_chain : hoare[Chain.chain : size X = n ==> size res.`1 = n].
proof.
proc.
sp.
wp.
while (size t = n); last by auto => />.  
seq 3 : (#pre). auto. 
seq 3 : (#pre /\ size _key = n).
  + auto => />. call size_prf. skip => />.
seq 1 : (#pre /\ size bitmask = n). 
  + auto => />. call size_prf. skip => />.
auto => />. 
call size_F.
skip => />. 
qed.

lemma ssize_chain : phoare[Chain.chain : size X = n ==> size res.`1 = n] = 1%r 
    by conseq chain_ll size_chain; auto => />. 
