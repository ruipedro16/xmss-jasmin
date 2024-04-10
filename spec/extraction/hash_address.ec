require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array8.
require import WArray32.



module M = {
  proc _zero_address (addr:W32.t Array8.t) : W32.t Array8.t = {
    var aux: int;
    
    var i:int;
    
    aux <- (8 %/ 2);
    i <- 0;
    while (i < aux) {
      addr <-
      Array8.init
      (WArray32.get32 (WArray32.set64 (WArray32.init32 (fun i_0 => (addr).[i_0])) i ((W64.of_int 0))));
      i <- i + 1;
    }
    return (addr);
  }
  
  proc __set_layer_addr (addr:W32.t Array8.t, layer:W32.t) : W32.t Array8.t = {
    
    
    
    addr.[0] <- layer;
    return (addr);
  }
  
  proc __set_tree_addr (addr:W32.t Array8.t, tree:W64.t) : W32.t Array8.t = {
    
    var t:W64.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var  _0:bool;
    
    t <- tree;
    (_of_, _cf_, _sf_,  _0, _zf_, t) <- SHR_64 t (W8.of_int 32);
    addr.[1] <- (truncateu32 t);
    addr.[2] <- (truncateu32 tree);
    return (addr);
  }
  
  proc __set_type (addr:W32.t Array8.t, type_0:W32.t) : W32.t Array8.t = {
    
    
    
    addr.[3] <- type_0;
    return (addr);
  }
  
  proc __set_key_and_mask (addr:W32.t Array8.t, key_and_mask:W32.t) : 
  W32.t Array8.t = {
    
    
    
    addr.[7] <- key_and_mask;
    return (addr);
  }
  
  proc __set_ots_addr (addr:W32.t Array8.t, ots:W32.t) : W32.t Array8.t = {
    
    
    
    addr.[4] <- ots;
    return (addr);
  }
  
  proc __set_chain_addr (addr:W32.t Array8.t, chain:W32.t) : W32.t Array8.t = {
    
    
    
    addr.[5] <- chain;
    return (addr);
  }
  
  proc __set_hash_addr (addr:W32.t Array8.t, hash:W32.t) : W32.t Array8.t = {
    
    
    
    addr.[6] <- hash;
    return (addr);
  }
  
  proc __set_ltree_addr (addr:W32.t Array8.t, ltree:W32.t) : W32.t Array8.t = {
    
    
    
    addr.[4] <- ltree;
    return (addr);
  }
  
  proc __set_tree_height (addr:W32.t Array8.t, tree_height:W32.t) : W32.t Array8.t = {
    
    
    
    addr.[5] <- tree_height;
    return (addr);
  }
  
  proc __set_tree_index (addr:W32.t Array8.t, tree_index:W32.t) : W32.t Array8.t = {
    
    
    
    addr.[6] <- tree_index;
    return (addr);
  }
}.

