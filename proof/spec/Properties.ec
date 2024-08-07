pragma Goals : printall.

require import AllCore List Distr RealExp IntDiv.
require (*  *) Subtype.

from Jasmin require import JModel.

require import Params Notation Address Primitives Wots XMSS.
require import XMSS_IMPL.

require import Array8.

import DList.
import NBytes.

(******************************************************* THASH_ *******************************************************)

op thash_f (address : adrs, _seed : seed, t : nbytes) : nbytes =
    let address = set_key_and_mask address 0 in
    let _key = PRF _seed address in
    let address = set_key_and_mask address 1 in
    let bitmask = PRF _seed address in
    F _key (nbytexor t bitmask).
