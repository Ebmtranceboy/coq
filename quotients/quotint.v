Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice seq.
Require Import generic_quotient.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope quotient_scope.

(*
Module FirstPresentation.

Definition int_axiom (z : nat * nat) := (z.1 == 0) || (z.2 == 0).
Definition int := {z | int_axiom z}. 

Definition reprZ (n : int) : nat * nat := val n.

Lemma sub_int_axiom x y : int_axiom (x - y, y - x).
Proof. by rewrite /int_axiom /= !subn_eq0; case: leqP => // /ltnW. Qed.

Definition piZ (x : nat * nat) : int :=
  exist _ (x.1 - x.2, x.2 - x.1) (sub_int_axiom _ _).

Lemma reprZK x : piZ (reprZ x) = x.
Proof.
rewrite /reprZ /=; apply: val_inj => /=.
case: x=> [[a b]]; rewrite /int_axiom /=.
by case/orP => [] /eqP->; rewrite !(subn0, sub0n).
Qed.

Definition int_quotClass := QuotClass reprZK.
Definition int_quotType := QuotType int int_quotClass.

Canonical Structure int_quotType.

Definition add x y := (x.1 + y.1, x.2 + y.2).
Definition addz (X Y : int)  := \pi_int (add (repr X) (repr Y)).
Lemma addz_compat : {morph \pi_int : x y / add x y >-> addz x y}.
Proof.
move=> [n1 d1] [n2 d2] /=; rewrite /addz /=.
apply: val_inj => /=; rewrite !unlock /=; symmetry.
have addnBACA x x' y y' : x' <= x -> y' <= y ->
  (x - x') + (y - y') = x + y - (x' + y').
  by move=> hx hy; rewrite addnBA // addnC addnBA // addnC subnDA.
have subnBACA x x' y y' : x' <= x -> y <= y' ->
  (x - x') - (y' - y) = x + y - (x' + y').
  by move=> hx hy; rewrite -subnDA addnBA // subnBA ?(leq_trans hy, leq_addl).
have subnBACAC x x' y y' : x' <= x -> y <= y' ->
  (x - x') - (y' - y) = y + x - (y' + x').
  by move=> hx hy; rewrite subnBACA // [y + x]addnC [y' + x'] addnC.
have [n1d1|/ltnW n1d1] := leqP d1 n1; rewrite (eqP n1d1) add0n;
have [n2d2|/ltnW n2d2] := leqP d2 n2; rewrite (eqP n2d2)
  ?(addn0, add0n, subn0, sub0n); congr (_, _);
do ?by [rewrite (eqP (leq_add _ _)) | rewrite addnBACA
       |rewrite subnBACA           | rewrite subnBACAC].
Qed.

Definition zeroz := \pi_int (0, 0).

Canonical zeroz_pi := @EqualTo _ zeroz zeroz erefl.

Lemma addz_pi (x y : nat * nat) (X : {pi x}) (Y : {pi y}) :
\pi_int (add x y) = addz (equal_val X) (equal_val Y).
Proof. by rewrite !piE addz_compat. Qed.

Canonical addz_equal_to (x y : nat * nat)
   (X : {pi x}) (Y : {pi y}) : {pi (add x y)} :=
  @EqualTo _ _  (addz (equal_val X) (equal_val Y)) (addz_pi X Y).


Lemma add0z x : addz zeroz x = x.
Proof. by rewrite -[x]reprK piE /add /= add0n -surjective_pairing. Qed.

End FirstPresentation.
*)

(* Alternatively *)
(* Canonical addz_equal_to' := PiMorph2 addz_compat. *)

Module SecondPresentation.

Definition equivnn (x y : nat * nat) := x.1 + y.2 == y.1 + x.2.

Lemma equivnn_refl : reflexive equivnn.
Proof. by move=> x; apply: eqxx. Qed.

Lemma equivnn_sym : symmetric equivnn.
Proof. by move=> x y; apply: eq_sym. Qed.

Lemma equivnn_trans : transitive equivnn.
Proof.
move=> y x z /eqP exy /eqP eyz.
rewrite /equivnn -(eqn_add2l y.2) addnC addnAC exy addnAC eyz.
by rewrite addnC addnCA addnA addnC.
Qed.

Canonical Structure equivnn_equiv : equiv_rel _ :=
  EquivRel equivnn equivnn_refl equivnn_sym equivnn_trans.

Definition int := {eq_quot equivnn}.
Canonical int_quotType := [quotType of int].

Definition add x y := (x.1 + y.1, x.2 + y.2).
Definition addz := lift_op2 int add.
Lemma addz_compat : {morph \pi_int : x y / add x y >-> addz x y}.
Proof.
move=> x y /=; rewrite /addz /= -!lock; apply/eqmodP; rewrite /= /equivnn /=.
apply/eqP; symmetry; rewrite addnACA.
have eq_repr u : repr (\pi_int u) = u %[mod int] by rewrite reprK.
have [/eqmodP /eqP -> /eqmodP /eqP ->] := (eq_repr x, eq_repr y).
by rewrite addnACA.
Qed.
Canonical addz_equal_to := PiMorph2 addz_compat.

Definition zeroz := lift_cst int (0, 0).
Canonical zeroz_pi := PiConst zeroz.

Lemma add0z x : addz zeroz x = x.
Proof. by rewrite -[x]reprK piE /add /= add0n -surjective_pairing. Qed.

(*
End SecondPresentation.
*)