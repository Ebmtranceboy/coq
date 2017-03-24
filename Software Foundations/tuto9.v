Inductive yesno : Set :=
  | yes : yesno
  | no : yesno.
Check yesno_ind.

Inductive ExSet : Type :=
  | con1 : bool -> ExSet
  | con2 : nat -> ExSet -> ExSet
  .

Check ExSet_ind.

(*
ExSet_ind
     : forall P : ExSet -> Prop,
       (forall b : bool, P (con1 b)) ->
       (forall (n : nat) (e : ExSet), P e -> P (con2 n e)) ->
       forall e : ExSet, P e

*)

Lemma plus_neutralR : forall m : nat, m + 0 = m.
Proof.
(intros ** ).
(induction m).
 reflexivity.
 (rewrite <- IHm).
 (simpl).
 (rewrite IHm).
 (rewrite IHm).
 reflexivity.

Qed.

Inductive beautiful : nat -> Prop :=
  b_0 : beautiful 0
| b_3 : beautiful 3
| b_5 : beautiful 5
| b_sum : forall n m,
       beautiful n -> 
            beautiful m -> 
                 beautiful (n+m).

Check beautiful_ind.
(*

beautiful_ind
     : forall P : nat -> Prop,
       P 0 ->
       P 3 ->
       P 5 ->
       (forall n m : nat,
        beautiful n -> P n -> beautiful m -> P m -> P (n + m)) ->
       forall n : nat, beautiful n -> P n


*)

Lemma one_not_beautiful: 
      forall n, n = 1 -> not (beautiful n).
Proof.
intros n E H.
induction H as [| | | p q Hp IHp Hq IHq].
inversion E. inversion E. inversion E.
destruct p as [|p']. destruct q as [|q'].
inversion E.
apply IHq. apply E.
destruct q as [|q'].
apply IHp.
rewrite plus_neutralR in E. exact E.
simpl in E. inversion E. destruct p'.
inversion H0. inversion H0.
Qed.

Lemma one_not_beautiful': not (beautiful 1).
Proof.
intros H.
remember 1 as n eqn:E.
apply one_not_beautiful in E. apply E. apply H.
Qed.
