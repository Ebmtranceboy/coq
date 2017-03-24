
Section Polymorphism.

Fixpoint length' {X:Type} (l:list X) : nat :=
  match l with
  | nil => 0
  | cons h t => S (length' t)
  end.

Notation "x :: y" := (cons x y)(at level 60, right associativity).

Fixpoint repeat {X : Type} (n : X) (count : nat) : list X :=
  match count with
  | 0 => nil
  | S k => n :: repeat n k 
  end.
  
Example test_repeat1:
  repeat true 2 = cons true (cons true nil).
  
Proof.
(simpl).
reflexivity.

Qed.

Theorem nil_app : forall X:Type, forall l:list X,
  app nil l = l.

Proof.
(intros **).
(simpl).
reflexivity.

Qed.

Fixpoint snoc {X:Type} (l:list X) (v:X) : (list X) :=
  match l with
  | nil => cons v nil
  | cons h t => cons h (snoc t v)
  end.

Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil => nil
  | cons h t => snoc (rev t) h
  end.

Theorem rev_snoc : forall X : Type,
                     forall v : X,
                     forall s : list X,
  rev (snoc s v) = cons v (rev s).
  
Proof.
(induction s).
 (simpl).
 reflexivity.

 (simpl).
 (rewrite IHs).
 (simpl).
 reflexivity.

Qed.

Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.

Proof.
(induction l).
 (simpl).
 reflexivity.

 (simpl).
 (rewrite rev_snoc).
 (rewrite IHl).
 reflexivity.

Qed.

Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Theorem snoc_with_append : forall X : Type,
                         forall l1 l2 : list X,
                         forall v : X,
  snoc (l1 ++ l2) v = l1 ++ (snoc l2 v).

Proof.
(intros **).
(induction l1).
 (simpl).
 reflexivity.

 (simpl).
 (rewrite IHl1).
 reflexivity.

Qed.

Notation "X >< Y" := (prod X Y)(at level 50) : type_scope.

Definition plus3 (n : nat) := 3 + n.

Theorem unfold_example : forall m n,
  3 + n = m ->
  plus3 n + 1 = m + 1.

Proof.
(intros m n H).
(unfold plus3).
(rewrite H).
reflexivity.

Qed.


