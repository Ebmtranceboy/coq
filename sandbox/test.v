Definition excluded_middle := forall P:Prop,  P \/ not P.

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    not (exists x, not (P x)) -> (forall x, P x).
Proof.
intros.
unfold not in H0.
unfold excluded_middle in H.
assert (P x \/ not (P x)).
apply H.
destruct H1.
apply H1.
destruct H0.
exists x.
apply H1.
Qed.
