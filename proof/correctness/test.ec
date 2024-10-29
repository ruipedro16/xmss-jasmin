require import AllCore.

lemma test : forall x y, x + 2 * y <= 4 && 2 * x + y <= 4 => x + y < 3.
proof.
coq edit "test" ().
qed.
