
Require Import Relations Relation_Operators.
Require Import Wf_nat.


Section Bad_hypothesis.

(** Let's assume the union of any pair of well-founded relations is 
    well founded too ... *)

Hypothesis union_wf : forall {A:Type}(R S: relation A),
                      well_founded R -> 
                      well_founded S ->
                      well_founded (union A R S).

(** Les us build a counter-example ... *)
Definition  R0  : relation nat := fun x y : nat => x = 2 /\ y = 1.


Lemma R0_wf : well_founded  R0.
Proof.
 intros x; split.
 intros y Hy; destruct Hy; subst x y.
 - split.
  + destruct  1; discriminate.
Qed.

(** By our hypothesis, the union of Peano's lt and R0 would be well-founded *)
Definition R1 := union _ lt R0.

Remark  R1_wf : well_founded R1.
Proof.
 unfold R1; apply union_wf.
 - apply lt_wf.
 - apply R0_wf.
Qed.

Lemma Acc_neg {A:Type}(R:relation A) : 
          forall x, Acc R x -> forall y, R y x ->  ~ R x y.
induction 1.
intros y Hy H1; generalize (H0 y Hy x H1); intro; contradiction.
Qed.


Lemma F : False.
Proof. 
 specialize  (Acc_neg  R1 1); intro H; apply H with 2.  
 - apply R1_wf.
 - right; now constructor.
 - left;auto with arith.
Qed.




End Bad_hypothesis.


