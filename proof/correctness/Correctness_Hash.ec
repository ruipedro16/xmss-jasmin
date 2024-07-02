pragma Goals : printall.

require import AllCore List RealExp IntDiv.
from Jasmin require import JModel.

require import XMSS_IMPL_PP XMSS_IMPL.
require import Address Notation Primitives.

require import Array8 Array32.

import NBytes.

lemma thash_f_correct (_out_ : W8.t Array32.t, _pub_seed_ : W8.t Array32.t, _addr_ : W32.t Array8.t) :
    equiv [Mp(Syscall).__thash_f ~ Chain.thash :
      arg{1}=(_out_, _pub_seed_, _addr_) /\ arg{2}=(to_list _out_, _addr_, to_list _pub_seed_) ==>
       res{2}.`1 = to_list res{1}.`1 /\ res{1}.`2 = res{2}.`2].
proof.
proc.
admit.
qed.

(* axiom sobre prf keygen *)
(* axiom sobre prf e F *)
