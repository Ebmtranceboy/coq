Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Theorem silly5 : forall (n m o : nat),
     [n;m] = [o;o] ->
     [n] = [m].
Proof.
(intros **).
(inversion H).
reflexivity.

Qed.

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
    x = y -> f x = f y.
Proof. intros A B f x y eq. rewrite eq. reflexivity. Qed.

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.
 
Theorem beq_nat_0_l : forall n,
   beq_nat 0 n = true -> n = 0.
Proof.
(intros n).
(unfold beq_nat).
(destruct n).
 (intros **).
 reflexivity.

 (intros **).
 discriminate H.

Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
(intros ** ).
(induction n).
 reflexivity.
 (simpl).
 (rewrite IHn).
 reflexivity.

Qed.

Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
 intros n. induction n as [| n']; intros; simpl in *.
    (* Hint: use the plus_n_Sm lemma *)
  destruct m; inversion H; subst; reflexivity.
  rewrite <- plus_n_Sm in H.
  destruct m. inversion H. simpl in H.
  rewrite <- plus_n_Sm in H. inversion H.
  apply IHn' in H1. rewrite -> H1. reflexivity.
Qed.

