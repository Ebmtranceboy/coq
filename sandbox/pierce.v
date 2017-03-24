Definition pierce := forall (p q : Prop),
  ((p -> q) -> p) -> p.
  
Definition lem := forall p, p \/ ~ p.

Theorem pierce_equiv_lem: pierce <-> lem.
Proof.
  unfold pierce, lem.
  firstorder.
  apply H with (q := ~ (p \/ ~ p)).
  firstorder.
  destruct (H p).
  assumption.
  tauto.
Qed.