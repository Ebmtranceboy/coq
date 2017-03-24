Require Import Arith.

Fixpoint sum_n n :=
  match n with
  | 0 => 0
  | S p => p + sum_n p
  end.

Lemma proof_by_ring : forall n, 2 * sum_n n + n = n * n.
Proof.
intros.
induction n.
simpl.
reflexivity.
assert (SnSn : S n * S n = n * n + 2 * n + 1).
ring.
rewrite SnSn.
rewrite <- IHn.
simpl.
ring.
Qed.

