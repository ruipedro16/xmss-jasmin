pragma Goals : printall.


require import AllCore List Distr RealExp IntDiv.
require (*  *) Subtype.

from Jasmin require import JModel.

require import Notation Address Primitives Wots.

import DList.
import NBytes.

(******************************************************************************)

(* Given a list [(a, b)], maps f over 'a's *)
(* Same as map (first f) in Haskell        *)
op map1 ['a] (f : nbytes -> nbytes) (xs : (nbytes * nbytes) list) =
    with xs = [] => []
    with xs = h::t => (f h.`1, h.`2) :: (map1 f t).


op from_int_list (x : int list) : byte list = map W8.of_int x.

(******************************************************************************)

op sample_n_bytes : nbytes distr = DList.dlist W8.dword n.

op genSKWots : wots_sk distr = DList.dlist sample_n_bytes len.
