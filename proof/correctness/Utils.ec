require import AllCore List RealExp IntDiv.

from Jasmin require import JModel.

lemma lte_lt (a b : int) :
    a <= b => a < b \/ a = b by smt().

lemma neg_lt (x y : int) : ! (x < y) <=> y <= x by smt().

lemma plus_lt (a b c : int) :
    a + b < c <=> b < (c - a) by smt().

lemma add_u (a b c : int) :
    a + b = a + c <=> b = c by smt().

pred valid_ptr(base_ptr offset : W64.t) = 
  0 <= to_uint offset => 
    0 <= to_uint base_ptr /\ to_uint (base_ptr + offset) < W64.modulus.
