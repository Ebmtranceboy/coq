Add LoadPath "Documents/coq/Software Foundations".
Require Export SfLib.

Definition relation (X: Type) := X->X->Prop.

(* Print le.
 ====> Inductive le (n : nat) : nat -> Prop :=
         le_n : n <= n | le_S : forall m : nat, n <= m -> n <= S m
Check le : nat -> nat -> Prop.
Check le : relation nat.
*)

Definition partial_function {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

(* Print next_nat.
   ====> Inductive next_nat (n : nat) : nat -> Prop := 
           nn : next_nat n (S n) 
Check next_nat : relation nat.
*)

Theorem next_nat_partial_function :
   partial_function next_nat.
Proof.
  unfold partial_function.
  intros x y1 y2 H1 H2.
  inversion H1. inversion H2.
  reflexivity. Qed.

Theorem le_not_a_partial_function :
  not (partial_function le).
Proof.
  unfold not. unfold partial_function. intros Hc.
  assert (0 = 1) as Nonsense.
   Case "Proof of assertion".
   apply Hc with (x := 0).
     apply le_n.
     apply le_S. apply le_n.
  inversion Nonsense. Qed.

Print total_relation_ind.

Theorem total_relation_not_a_partial_function :
  not (partial_function total_relation).
Proof.
unfold not. unfold partial_function. intros Hc.
assert (0=1) as Nonsense. 
apply Hc with (x:=0). apply tot. apply tot. discriminate Nonsense.
Qed.

Print empty_relation_ind.

Theorem empty_relation_partial_function :
  partial_function empty_relation.
Proof.
unfold partial_function.
  intros x y1 y2 H1 H2.
  inversion H1. 
Qed.

Definition reflexive {X: Type} (R: relation X) :=
  forall a : X, R a a.

Theorem le_reflexive :
  reflexive le.
Proof.
  unfold reflexive. intros n. apply le_n. Qed.

Definition transitive {X: Type} (R: relation X) :=
  forall a b c : X, (R a b) -> (R b c) -> (R a c).

Theorem le_trans :
  transitive le.
Proof.
  intros n m o Hnm Hmo.
  induction Hmo.
  Case "le_n". apply Hnm.
  Case "le_S". apply le_S. apply IHHmo. Qed.

Theorem lt_trans:
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  apply le_S in Hnm.
  apply le_trans with (a := (S n)) (b := (S m)) (c := o).
  apply Hnm.
  apply Hmo. Qed.

Theorem le_Sn_le : forall n m, le (S n) m -> le n m.
Proof.
  intros n m H. apply le_trans with (S n).
    apply le_S. apply le_n.
    apply H. Qed.

Theorem le_S_n : forall n m, le (S n) (S m) -> le n m.
Proof.
intros. inversion H. apply le_n.
apply le_Sn_le in H1. exact H1.
Qed.

Theorem le_Sn_n : forall n,
  not (S n <= n).
Proof.
intros. unfold not. intros. inversion H. inversion H0. rewrite le_Sn_le with (m:=n).


