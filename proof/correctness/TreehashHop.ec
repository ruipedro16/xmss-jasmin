pragma Goals : printall.


require import AllCore List RealExp IntDiv Distr DList.
require (*--*) Subtype. 

from Jasmin require import JModel.
 
require import Types XMSS_MT_Types Address Hash LTree WOTS.
import XMSS_MT_Params Params.

module TreeHashHop = {
  proc treehash(pub_seed sk_seed : seed, s t : int, address : adrs) : nbytes = {
    var node : nbytes;
    var stack : nbytes list <- nseq ((h %/ d) + 1) (NBytes.insubd (nseq n W8.zero));
    var heights : int list <- nseq (h %/ d) witness; (* Used to manage the height of nodes *)
    var pk : wots_pk;
    var offset : int;
    var i, j : int;
    var tree_index : W32.t;
    var node0, node1, new_node : nbytes;
    
    var node_address : adrs <- set_type address 2;
    
    offset <- 0;
    i <- 0;
    while (i < 2^t) {
      address <- set_type address 0;
      address <- set_ots_addr address (s + i);

      (* Generate the public key from the secret seed *)
      pk <@ WOTS.pkGen(sk_seed, pub_seed, address);

      address <- set_type address 1;
      address <- set_ltree_addr address (s + i);

      (* compress the WOTS public key into a single N-byte value *)
      node <@ LTree.ltree(pk, address, pub_seed); 

      stack <- put stack offset node; (* Push the node onto the stack *)
      offset <- offset + 1;
      heights <- put heights (offset - 1) 0;
      
      while (
          2 <= offset /\ (* The stack needs to have at least two nodes *)
          nth witness heights (offset - 1) = nth witness heights (offset - 2)
      ) {

        tree_index <- W32.of_int(s + i) `>>>` ((nth witness heights (offset - 1)) + 1);
        
        node_address <- set_tree_height address (nth witness heights (offset - 1));
        node_address <- set_tree_index address (W32.to_uint tree_index);

        node0 <- nth witness stack (offset - 2);
        node1 <- nth witness stack (offset - 1);

        new_node <@ Hash.rand_hash(node0, node1, pub_seed, address);

        stack <- put stack (offset - 2) new_node; (* push new node onto the stack *)
        offset <- offset - 1; (* One less node on the stack (removed node0 and node1 and added new_node) *)
        heights <- put heights (offset - 1) (nth witness heights (offset - 1)); (* The new node is one level higher than the nodes used to compute it *)
      }      

      i <- i + 1;
    }

    node <- nth witness stack 0;
    return node;
  }
}.
