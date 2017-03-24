Module Playground1.

Inductive bool : Type :=
  | true : bool
  | false : bool.

Definition negb (b:bool) : bool := 
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool := 
  match b1 with 
  | true => b2 
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool := 
  match b1 with 
  | true => true
  | false => b2
  end.
Definition nandb (b1:bool) (b2:bool) : bool :=
   negb (andb b1 b2).

Example test_nandb1: (nandb true false) = true.
Proof. reflexivity. Qed.
End Playground1.

(*
Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.
*)

Fixpoint factorial (n:nat) : nat := 
  match n with
    | O => 1
    | (S m) => mult n (factorial m)
  end.

Eval compute in (factorial 5).

Theorem plus_id_example : forall n m:nat,
  n = m -> 
  n + n = m + m.

Proof.
  intros n m. (* move both quantifiers into the context *)
  intros H. (* move the hypothesis into the context *)
  rewrite <- H. (* Rewrite the goal using the hypothesis read from right to left*)
  reflexivity. Qed.
