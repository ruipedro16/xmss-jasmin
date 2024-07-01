require import AllCore List RealExp IntDiv.

from Jasmin require import JModel.

pred valid_ptr (p o : W64.t) = 
  0 <= to_uint o => 
    0 <= to_uint p /\ to_uint (p + o) < W64.modulus.
