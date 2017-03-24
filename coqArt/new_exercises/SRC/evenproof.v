Require Import Arith Omega.

Fixpoint exp2 (n:nat) : nat :=
  match n with 0 => 1
             | S p => 2 * (exp2 p)
  end.

Fixpoint tower2 (n:nat) : nat :=
  match n with 0 => 1
             | S p => exp2 (tower2 p)
  end.


(** Test :

Compute tower2 3.

*)



Inductive even : nat -> Prop :=
  even0 : even 0
| even_S : forall p, even p -> even (S (S p)).

Hint Constructors even.


Theorem even_double : forall n, even (2*n).
Proof.
 induction n as [ | n IHn].
 - cbn; constructor. 
 - cbn in IHn; cbn.
   rewrite <- plus_n_Sm; now constructor.
Qed.

Hint Resolve even_double.

Theorem even_exp2 : forall n, 0 < n -> even (exp2 n).
Proof.  
 intro n; case n as [ | n].
 -  inversion 1.
 -  intros _; change (even (2 * (exp2 n)));auto.
Qed.

Theorem exp2_positive : forall n, 0 < exp2 n.
Proof.
 induction n as [ | n IHn].
 - cbn;auto.
 - cbn; omega. 
Qed.

Theorem even_tower2 : forall n, 0 < n -> even (tower2 n).
Proof.
 intro n; case n as [ | p].
 -  inversion 1.
 - cbn; intros; apply even_exp2.  
   case p; [ cbn;auto | intros;apply exp2_positive].
Qed.


Lemma six_tower : even (tower2 6).
 apply even_tower2;  auto with arith.
Qed.



 
 
