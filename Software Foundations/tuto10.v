Check ex.
Print nat_rect.

Definition nat_ind2 :
    forall (P : nat -> Prop),
    P 0 ->
    P 1 ->
    (forall n : nat, P n -> P (S(S n))) ->
    forall n : nat , P n :=
       fun P => fun P0 => fun P1 => fun PSS =>
          fix f (n:nat) := match n with
                             0 => P0
                           | 1 => P1
                           | S (S n') => PSS n' (f n')
                          end.

Load "/home/joel/Documents/coq/Software Foundations/SfLib.v".
Print ev.

(*

Inductive ev : nat -> Prop :=
  | ev_0 : ev O
  | ev_SS : forall n:nat, ev n -> ev (S (S n)).

*)

Fixpoint even (n:nat) :=
  match n with
  | 0 => True
  | S 0 => False
  | S (S m) => even m
  end.

Lemma even__ev : forall n, even n -> ev n.
Proof.
 intros.
 induction n as [ | |n'] using nat_ind2.
  Case "even 0".
    apply ev_0.
  Case "even 1".
    inversion H.
  Case "even (S(S n'))".
    apply ev_SS.
    apply IHn'. unfold even. unfold even in H. simpl in H. apply H.
Qed.
