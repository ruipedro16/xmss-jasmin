pragma Goals : printall.

require import AllCore List RealExp IntDiv.
require (*  *) Subtype. 
from Jasmin require import JModel.

require import XMSS_MT_Types XMSS_MT_Params XMSS_MT_Notation XMSS_MT_Address XMSS_MT_Hash XMSS_MT_Util.
require import Array8.

module Chain = {
   proc chain(X : nbytes, i s : int, _seed : seed, address : adrs) : nbytes * adrs = {
      (*
       *
       * i: start index
       * s: number of steps
       *
       *)
    var t : nbytes <- X;
    var chain_count : int <- 0;
    var _key : key;
    var bitmask : nbytes;
    var addr_bytes : W8.t list;

    (* case i + s <= w-1 is precondition *)
    while (chain_count < s) {
     address <- set_hash_addr address (i + chain_count);
     address <- set_key_and_mask address 0;
      
      addr_bytes <- addr_to_bytes address;
     _key <@ Hash.prf(addr_bytes, _seed);
     
     address <- set_key_and_mask address 1;
      
     addr_bytes <- addr_to_bytes address;
     bitmask <@ Hash.prf(addr_bytes, _seed);

     t <@ Hash._F (_key, (nbytexor t bitmask));
     
     chain_count <- chain_count + 1;
    }
    
    return (t, address);
   }
}.

pred chain_pre(X : nbytes, i s : int, _seed : seed, address : adrs) = 
    0 <= s <= w-1.
