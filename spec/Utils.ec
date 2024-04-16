
require import AllCore List Distr RealExp IntDiv.

from Jasmin require import JModel.

require import Array32.

pragma Goals : printall.

abbrev (<=) (a b : W64.t) = W64.to_uint a <= W64.to_uint b.

module M = {
    proc __memcmp (a:W8.t Array32.t, b:W8.t Array32.t) : W64.t = {
        var r:W64.t;
        var are_equal:W64.t;
        var acc:W8.t;
        var i:W64.t;
        var t:W8.t;
        var _of_:bool;
        var _cf_:bool;
        var _sf_:bool;
        var zf:bool;
        var  _0:bool;
        var  _1:W8.t;

        r <- (W64.of_int (- 1));
        are_equal <- (W64.of_int 0);
        acc <- (W8.of_int 0);
        i <- (W64.of_int 0);

        while ((i \ult (W64.of_int 32))) {
          t <- a.[(W64.to_uint i)];
          t <- (t `^` b.[(W64.to_uint i)]);
          acc <- (acc `|` t);
          i <- (i + (W64.of_int 1));
        }

        (_of_, _cf_, _sf_,  _0, zf,  _1) <- AND_8 acc acc;
        r <- (zf ? are_equal : r);
        return (r);
  }
}.

op mkarray : 'a list -> 'a Array32.t. (* This is from Array theory ? *)

op memcmp (a b : W8.t list) : bool = a = b.

op int_of_bool (b : bool) : int = if b then 0 else -1.

lemma memcmp_imp_fun (a b : W8.t list) :
    hoare [M.__memcmp : arg = (mkarray a, mkarray b) ==> res = W64.of_int (int_of_bool (memcmp a b))].
proof.
proc.
auto.
while (W64.zero <= i <= W64.of_int 32).
  - simplify. admit.
  - progress. admit.
qed.
