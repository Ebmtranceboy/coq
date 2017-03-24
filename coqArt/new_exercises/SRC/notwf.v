Require Import ClassicalChoice.

Section not_wf_with_choice.

 Variables (A:Set)(R: A -> A -> Prop).
 Hypothesis R_not_wf : not (well_founded R).

 Notation "x > y" := (R y x).

 Definition strictly_decreasing (seq: nat -> A) :=
  forall n :nat, seq n > seq (S n).


  Remark  ex_not_acc :  exists x:A, ~ (Acc R x).
  Proof.
   apply not_all_ex_not;auto.
  Qed.
 
 
 Lemma go_down : forall x, ~ Acc R x -> exists y, x > y /\ ~ Acc R y.
 Proof.
 intros x H; change (exists z, (fun y => x > y /\ ~ Acc R y) z).
 apply not_all_not_ex.
 intro H0;  assert (H1: forall n, x > n -> Acc R n).
 -  intros n Hn;  specialize (H0 n).
     case (not_and_or _ _ H0).
    +  now destruct 1.
    +  intros;apply NNPP;auto. 
 -  apply H; split;apply H1.
 Qed.


 Lemma decrease : exists f, 
       forall x, ~ Acc R x ->  ~ Acc R (f x) /\ x > f x.
 Proof.
 case (choice  (fun x y =>  Acc R x \/ x > y /\ ~ Acc R y)).
 -  intros x ; case (classic (Acc R x)).
   +  exists x;auto.
   + intros H; case (go_down _ H).
     intros x0 [Hx0 H'x0]; exists x0; auto. 
 - intros s Hs; exists s.
   intros x;  case (Hs x); tauto.
Qed.

Theorem infinite_descent : exists s : nat -> A, strictly_decreasing  s.
Proof.
  destruct decrease as [s Hs].
  case ex_not_acc;intros z0 Hz.
  pose (F := fun n:nat => Nat.iter n s z0); exists F.
  assert (H : forall n, F n > F (S n) /\ ~ Acc R (F n) /\ ~ Acc R (F (S n))).
  - induction n as [| p IHp].
   + unfold F; case (Hs z0 Hz);  tauto.
   +  destruct IHp as [H [H0 H1]]; split; auto.
    simpl; now case (Hs _ H1).
    split;auto;    now case (Hs _ H1).
 -  simpl; red;  intros n; case (H n);simpl;auto.
Qed.

End not_wf_with_choice.





 
 
