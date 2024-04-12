require import AllCore List RealExp IntDiv.
require Subtype. 
from Jasmin require import JModel.
require import Notation Parameters.

type pk_t = byte list.
type sk_t = byte list.
type key_pair = pk_t * sk_t.

type sig_t = byte list.
type msg_t = byte list.

module type SignatureScheme = {
    proc keygen() : key_pair
    proc sign(sk : sk_t, m : msg_t) : sig_t * sk_t
    proc verify(pk : pk_t, m : msg_t, s : sig_t) : bool
}.
