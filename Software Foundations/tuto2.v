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
  
Theorem plus_1_neq_0 : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n. destruct n as [| n'].
    reflexivity.
    reflexivity. Qed.

Theorem identity_fn_applied_twice :
  forall(f : bool -> bool),
  (forall(x : bool), f x = x) ->
  forall(b : bool), f (f b) = b.
Proof.
(intros **).
(rewrite H).
(rewrite H).
reflexivity.

Qed.


Inductive bin : Type :=
  | Z : bin
  | D : bin -> bin
  | ID : bin -> bin.
  
Fixpoint incr (n : bin) : bin :=
  match n with
  | Z => ID Z
  | D n' => ID n'
  | ID n' => D (incr n')
  end.

Fixpoint double (n:nat) :=
match n with
| O => O
| S n' => 2 + (double n')
end.

Fixpoint bin_to_nat (n : bin) : nat :=
  match n with
  | Z => O
  | D n' => double (bin_to_nat n')
  | ID n' => 1 + (double (bin_to_nat n'))
  end.

Example test_bin_incr1 : 
  forall n :bin,
    1 + (bin_to_nat n) = bin_to_nat (incr n).
Proof.
(intros n).
(induction n).
 reflexivity.

 reflexivity.

 (simpl).
 (rewrite <- IHn).
 reflexivity.

Qed.

