
Fixpoint evf (n:nat) :=
  match n with
  | 0 => True
  | S 0 => False
  | S (S m) => evf m
  end.

Inductive evi : nat -> Prop :=
  | ev_0 : evi O
  | ev_SS : forall n:nat, evi n -> evi (S (S n)).

Theorem evi_evf : forall n,
  evi n -> evf n.
Proof.
intros n E.
induction E as [| n' E'].
 unfold evf.
 auto.

 unfold evf.
 apply IHE'.
Qed.

Theorem evf_evi : forall n,
  evf n -> evi n.
Proof.
Abort.

Theorem cons_app : forall (X:Type) (l1 l2:list X) (x:X),
  app (cons x l1) l2 = cons x (app l1 l2).
Proof.
intros.
induction l1.
 simpl.
 reflexivity.

 auto.

Qed.


Inductive subsequence : list nat -> list nat -> Prop :=
  | sseq_empty : forall q, subsequence nil q
  | sseq_fst : forall x b q, subsequence b q -> subsequence b (cons x q)
  | sseq_snd : forall x b q, subsequence b q -> subsequence (cons x b) (cons x q)
  .

Theorem cct_sseq : forall s t u, subsequence s t -> subsequence s (app t u).
Proof.
intros.
induction H.
 apply sseq_empty.

 rewrite cons_app.
 apply sseq_fst.
 apply IHsubsequence.

 rewrite cons_app.
 apply sseq_snd.
 apply IHsubsequence.

Qed.

Fixpoint true_upto_n__true_everywhere (x: nat) (f: nat -> Prop) :=
  match x with
  | 0 => forall m : nat, f m
  | S n => f x -> true_upto_n__true_everywhere n f
  end.

Example true_upto_n_example :
    (true_upto_n__true_everywhere 3 (fun n => evi n))
  = (evi 3 -> evi 2 -> evi 1 -> forall m : nat, evi m).
Proof. reflexivity.  Qed.


Inductive ex (X:Type) (P : X->Prop) : Prop :=
  ex_intro : forall(witness:X), P witness -> ex X P.

Notation "'exists' x , p" := (ex _ (fun x => p))
  (at level 200, x ident, right associativity) : type_scope.
Notation "'exists' x : X , p" := (ex _ (fun x:X => p))
  (at level 200, x ident, right associativity) : type_scope.

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> not (exists x, not ( P x)).
Proof.
intros.
unfold not.
intros.
inversion H0.
auto.
Qed.

Definition excluded_middle := forall P:Prop,  P \/ not P.

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    not (exists x, not (P x)) -> (forall x, P x).
Proof.
intros.
unfold not in H0.
unfold excluded_middle in H.
assert (P x \/ not (P x)).
apply H.
destruct H1.
apply H1.
destruct H0.
exists x.
apply H1.
Qed.4
