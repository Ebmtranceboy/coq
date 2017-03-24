Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.
  
Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.

Proof.
(intros **).
(destruct b).
 (simpl).
 (destruct c).
  (simpl).
  reflexivity.

  (simpl).
  auto.

 (destruct c).
  reflexivity.

  auto.

Qed.

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
(intros **).
(induction n).
 auto.
 (simpl).
 (apply IHn).

Qed.


Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => 2 + double n'
  end.

Fact plus_distr : forall n m: nat, S (n + m) = n + (S m).
Proof.
(intros **).
(induction n).
 reflexivity.
 (simpl).
 (rewrite IHn).
 reflexivity.

Qed.


Lemma double_plus : forall n, double n = n + n .

Proof.
(intros **).
(induction n).
 reflexivity.
 (simpl).
 (rewrite IHn).
 (rewrite plus_distr).
 reflexivity.

Qed.

Lemma plus_neutralR : forall m : nat, m + 0 = m.
Proof.
(intros ** ).
(induction m).
 reflexivity.
 (rewrite <- IHm).
 (simpl).
 (rewrite IHm).
 (rewrite IHm).
 reflexivity.

Qed.

Theorem plus_comm : forall n m : nat, n + m = m + n.
Proof.
(intros ** ).
(induction n).
 (simpl).
 (rewrite plus_neutralR).
 reflexivity.

 (simpl).
 (rewrite IHn).
 (rewrite plus_distr).
 reflexivity.

Qed.
