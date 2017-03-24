Inductive sumbool (A B : Prop) : Set :=
 | left : A -> sumbool A B
 | right : B -> sumbool A B.

Notation "{ A } + { B }" := (sumbool A B) : type_scope.


Theorem eq_nat_dec : forall n m : nat, {n = m} + {n <> m}.
Proof.
induction n. intros m.
destruct m.
left. reflexivity.
right. unfold not. intros. discriminate H. 

intros m.
destruct m.
right. intros contra. inversion contra.
destruct IHn with (m := m) as [eq | neq].
left. rewrite eq. reflexivity.
right. intros Heq. inversion Heq. auto. 
Defined.

(* APPLICATION *)

Definition override {X: Type} (f: nat->X) (k:nat) (x:X) : nat->X:=
  fun (k':nat) => if eq_nat_dec k k' then x else f k'.

Theorem override_same : forall (X:Type) x1 k1 k2 (f : nat->X),
  f k1 = x1 ->
  (override f k1 x1) k2 = f k2.
Proof. 
intros. unfold override. destruct (eq_nat_dec k1 k2).
rewrite e in H. symmetry. exact H. reflexivity.
Qed. 

Definition l := cons 4 (cons 5 nil).
Definition head {X: Type} (xs: list X) : option X := match xs with | nil => None | cons a ys => Some a end.

Eval compute in (head l).

Definition add1 : nat -> nat.
intro n.
Show Proof.
apply S.
Show Proof.
apply n. Defined.

Print add1.
 