require import AllCore List RealExp IntDiv.

from Jasmin require import JModel.

lemma lte_lt (a b : int) :
    a <= b => a < b \/ a = b by smt().

pred valid_ptr(p : int, o : int) = 
  0 <= o => 
    0 <= p /\ p + o < W64.modulus.
