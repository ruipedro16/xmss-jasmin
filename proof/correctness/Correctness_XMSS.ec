pragma Goals : printall.

require import AllCore List RealExp IntDiv.
from Jasmin require import JModel JArray.

require import Params Parameters Address Notation Primitives Wots XMSS_MT_PRF.
require import XMSS_IMPL XMSS_IMPL_HOP1 RandomBytes.

require import Array8 Array32 Array64.

(*** Randomized Hashing ***)
lemma thash_correct (_in : W8.t Array64.t,
                     _pub_seed : W8.t Array32.t, 
                     _addr:W32.t Array8.t) :
    equiv[M_Hop1(Syscall).__thash_h ~ RandHash.rand_hash : true ==> true].

(******* exported functions ********)
