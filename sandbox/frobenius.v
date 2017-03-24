Theorem frobenius (A : Set) (p : A -> Prop) (q : Prop) :
  (exists x : A, q /\ p x) <-> (q /\ exists x : A,p x).

Proof.
  split.
  intros [y [H1 H2]].
  split.
  assumption.
  exists y.
  assumption.
  intros [H1 [y H2]].
  exists y.
  auto.
Qed.