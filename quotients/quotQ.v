Inductive even : nat -> Prop:=
 | even_O: even O
 | even_S: forall n, even n -> even (S(S n)).

Lemma two_is_even:
  even (S (S O)).
Proof. 
constructor.
constructor.
Qed.


Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q.

Definition not (P:Prop) := P -> False.

Theorem double_neg : forall P : Prop,
  P -> not (not P).
Proof.

intros.
unfold not.
auto.
Qed.

Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (not Q -> not P).
Proof.  
intros.
unfold not.
auto.
Qed.

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
intros.
inversion H.
Qed.


Inductive positive_nat : nat -> Prop :=
  | p_nat1: positive_nat(S 0)
  | p_nat2: forall n, positive_nat n -> positive_nat(S n).



(*
Inductive int :=
  | zero_minus:   
*)

(*

Module Type MONAD.
 Set Implicit Arguments.
 Parameter M : forall (A : Type), Type.
 Parameter ret : forall (A : Type), A -> (M A).
 Parameter bind : forall (A B : Type), M A -> (A -> M B) -> M B.
End MONAD.

Definition flip : forall (a b c : Set), (a -> b -> c) -> b -> a -> c.
Proof.
tauto.
Defined.

Extraction Language Haskell.
Extraction flip.
*)

Definition ordered_pair := (nat * nat)%type.
Definition Z_axiom (z : ordered_pair) := (0 = fst z) /\ (0 = snd z).
Definition Z := {z | Z_axiom z}.



(*
Inductive Z : Type :=
*)
Definition reprP (z : ordered_pair) : nat * nat := pair (fst z) (snd z). 

(*
Definition reprZ (z : Z) : nat * nat := pair (fst z) (snd z). 

Require Import ssrfun. (* for .1 .2 *)
Require Import ssrnat. (* for 0 *)
Require Import ssrbool. (* for == 0 *)
Require Import eqtype. (* for == *)
Require Import ZArith.

Definition Q_axiom (q : Z * Z) := (Z.gcd q.1 q.2 == 1).
*)

(*
Notation "a .1" := (fst a) (at level 60).
Notation "a .2" := (snd a) (at level 60).
*)

(*
Require Import ssreflect choice seq.
Require Import ssrfun eqtype ssrbool ssrnat.
Require Import generic_quotient.
*)

(*
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope quotient_scope.

Module FirstPresentation.

Definition int_axiom (z : nat * nat) := (z.1 == 0) || (z.2 == 0).

End FirstPresentation.
*)

(*
Record ring_theory : Prop := mk_rt {
  Radd_0_l    : forall x, 0 + x == x;
  Radd_sym    : forall x y, x + y == y + x;
  Radd_assoc  : forall x y z, x + (y + z) == (x + y) + z;
  Rmul_1_l    : forall x, 1 * x == x;
  Rmul_sym    : forall x y, x * y == y * x;
  Rmul_assoc  : forall x y z, x * (y * z) == (x * y) * z;
  Rdistr_l    : forall x y z, (x + y) * z == (x * z) + (y * z);
  Rsub_def    : forall x y, x - y == x + -y;
  Ropp_def    : forall x, x + (- x) == 0
}.
*)