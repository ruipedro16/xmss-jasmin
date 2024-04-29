pragma Goals : printall.

(**********************************************************************************************************************)

require import Address Notation Parameters Primitives Properties Wots.

(* proof that the extracted EasyCrypt is equiavalent to the (preprocessed)1 EasyCrypt *)
(* The preprocessed EasyCrypt is the same as the extracted EasyCrypt, but replaces calls to core_hash with calls
   to an operator H *)

require import XMSS_IMPL.
require import XMSS_IMPL_PP.


