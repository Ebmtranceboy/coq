(** Midterm exam for 15414/614 s14 (100 points in total)**)

(******************************************************************************************
                   P1   |   P2   |   P3   |    P4   |   P5   |   P6   |   P7   |   P8    |   Total
_____________________________________________________________________
Full score |   10  |   10   |   10    |   10    |   10    |   10   |  10    |    30    |   100
_____________________________________________________________________
Your score|        |          |           |           |           |          |          |            |
_____________________________________________________________________

*****************************************************************************************) 

(** Due by 11:59pm March 2nd **)

(** Submit your solve to the TA via emails **)
(** A single .v (Coq) file is preferred for your submission **)

(*************************************************************************************
****************** Further Instructions ********************************************
*************************************************************************************

To prove some of the following theorems, you may need to first
prove some lemmas.
You are welcome to use whatever is proved in the class in
Basics.v, Induction.v, and Lists.v

For this exam, automatic tactics of Coq (auto, tauto, trivial,
intuition, omega, etc.) are not allowed.

Some hints about simpl and apply : To simplify a particular term t in
a proof goal, you can use `simpl (t)' - it will leave everything else unchanged.
To apply a known lemma L in a hypothesis H, use `apply L in H'.

You will get partial credit if you assert
something you need and use it without proving the assertion, as long as the
assertion is really true. 

During the take-home exam, no questions will be answered except the ones
w.r.t. the understanding of the given statements of the problem set.
**************************************************************************************
*************************************************************************************)



(***       Problem 1 : Fast SAT solving (10 points) *******************************

Recall the resolution rule discussed in class. 
Given two clauses C1 as C1' \/ p and C2 as C2' \/ ~p,
where p is an atomic proposition, resolution w.r.t. the automic proposition p
gives us a new clause C1' \/ C2' which is equisatisfiable to C1 /\ C2. 

Consider the following set of clauses, where p, q, r, and l are propositions. 
Show that it is unsatisfiable by applying the resolution rule only. 
{p \/ q, ~q, ~p \/ q \/ ~l, r \/ l, ~r \/ ~l, ~r \/ ~p}


[Let each clause be labeled as (1), (2), ..., (6).
Applying the resolution rule to some pairs of clauses...

(1)/\(2): (p \/ q) /\ (~q) -> p                        ...  (A)
(4)/\(6): (r \/ l) /\ (~r \/ ~p) -> (~p \/ l)          ...  (B)
(B)/\(3): (~p \/ l) /\ (~p \/ q \/ ~l) -> (~p \/ q)    ...  (C)
(C)/\(2): (~p \/ q) /\ (~q) -> ~p                      ...  (D)
(A)/\(D): p /\ (~p) -> False

Thus, the given set of clauses is unsatisfiable, as it eventually comes to
include False in the series of /\ operations.]

****************************************************************************************)

(***************************************************************************************
******************* I am a parting line, plz ignore me ******************************
***************************************************************************************)

Require Import List.
Require Import Arith.

(***            Problem 2: Propositional Logic in Coq (10 points)**********************
Prove the following theorems.
(Hint: you may need to import classical. Also, for some of them, you may need
to define and prove extra lemmas.)
*****************************************************************************************)
(* 2 points *)
Theorem ba : forall A B C : Prop, (A \/ B) /\ (~B \/ C) -> A \/ C.
Proof.
intros.
destruct H as [H1 H2].
destruct H1 as [HA | HB].
left.
assumption.
destruct H2 as [HnB | HC].
contradiction.
right.
assumption.
Qed.

(* 2 points *)
Require Import Classical.
Theorem bb : forall A B C: Prop, ((A /\ ~B -> C) /\ ~C ) /\ A -> B.
Proof.
intros.
destruct H as [[H1 H2] H3].
apply NNPP.
(*
A tactic for proof by contradiction. With contradict H,

    H:~A |- B gives |- A
    H:~A |- ~B gives H: B |- A
    H: A |- B gives |- ~A
    H: A |- ~B gives H: B |- ~A
    H:False leads to a resolved subgoal. Moreover, negations may be in unfolded forms, and A or B may live in Type

*)
contradict H1.
intro.
apply H2.
apply H.
split.
assumption.
assumption.
Qed.

(* 3 points *)
Theorem bc : forall A B C D: Prop, (A -> B) -> ((C -> D) -> (A /\ C -> B /\ D)).
Proof.
intros.
destruct H1 as [HA HC].
split.
apply H.
assumption.
apply H0.
assumption.
Qed.

(* 3 points *)
Theorem bd: 
forall (X : Set) (P : X -> Prop), ~(forall x, ~(P x)) -> (exists x, P x).
Proof.
intros.
apply NNPP.
intro.
apply H.
intro x. 
intro.
apply H0.
exists x.
assumption.
Qed.

(***************************************************************************************
******************* I am a parting line, plz ignore me ******************************
***************************************************************************************)

(***** Some definitions/notations for lists, as we saw in class *****)


(***     Problem 3: Lists in Coq (10 points )******************************************
Define the following operations on Lists. Please remeber to demonstrate
your definition is correct. (Hint: you may need to define extra
functions in order to complete the functions that you are requested.)
***************************************************************************************)

(*a (3 points)
Define the function "IsElem" that checks whether an element belongs to a nat
list.
*)

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

Fixpoint IsElem (a : nat) (l : list nat) : bool := 
match l with
nil => false
| head :: tail =>
if (beq_nat a head) then true else (IsElem a tail)
end.

Eval compute in (IsElem 3 (1::(2::(2::nil)))).
Eval compute in (IsElem 3 (1::(2::(3::nil)))).
Eval compute in (IsElem 3 nil).

(*b (3 points)
Define the function "DropDupElem" that, given a nat list, eleminates
extra copies
of all duplicated elements. For instance, given [2, 4, 2, 3, 5, 3, 5,
5], it should
return a list only contains one 2, one 4, one 3, and one 5. Notice that, there
is no constraint on the order of elements in the returned list.
*)

Fixpoint DropDupElem (l : list nat) : (list nat) :=
match l with 
nil => nil
| head :: tail =>
if (IsElem head tail) then (DropDupElem tail) else head :: (DropDupElem tail)
end.

Eval compute in (DropDupElem (1 :: 2 :: 3 :: 2 :: 1 :: 5 :: 4 :: 4 :: nil)).

(*c (4 points)
Recall the definition of IsElem in the previous subproblem.
Prove the following theorem:
Theorem List1c : forall (n : nat) (l : list nat), IsElem n
(DropDupElem l) = IsElem n l. *)

Theorem List1c : forall (n : nat) (l : list nat), IsElem n (DropDupElem l) = IsElem n l.
Proof.
intros.
induction l as [|h t].
reflexivity.

simpl.
assert (H1: IsElem h t = true \/ IsElem h t = false).
case (IsElem h t).
left. reflexivity.
right. reflexivity.

assert (H2: beq_nat n h = true \/ beq_nat n h = false).
case (beq_nat n h).
left. reflexivity.
right. reflexivity.

destruct H1 as [H1t | H1f].
destruct H2 as [H2t | H2f].
rewrite -> H1t.
rewrite -> H2t.
replace h with n in H1t.
rewrite <- IHt in H1t.
assumption.

(*Lemma beq_nat_true : forall x y, beq_nat x y = true -> x=y.*)
apply beq_nat_true.
assumption.

rewrite -> H1t.
rewrite -> H2f.
assumption.

rewrite <- IHt.
rewrite -> H1f.
simpl.
reflexivity.
Qed.



(***************************************************************************************
******************* I am a parting line, plz ignore me ******************************
***************************************************************************************)

(***   Problem 4: Play with Lists in Coq  (10 points)********************************)

(*a (2 points)
Define the function "MaxOfAList" that returns the maximal natural number in the
given nat list l. When l is empty, you can return 0. Please remeber to
demonstrate
your definition is correct. *)


Fixpoint blt_nat n1 n2 :=
  match n1, n2 with
    O, S n2' => true |
    S n1', S n2' => blt_nat n1' n2' |
    _, _ => false
  end.

Fixpoint MaxOfAList (l : list nat) : nat :=
  match l with
    nil => 0 |
    x::xs => let m := (MaxOfAList xs) in
      if blt_nat x m then m
      else x
    end.

Example MaxEmpty: MaxOfAList nil = 0.
reflexivity.
Qed.

Eval compute in (MaxOfAList (1::(2::(2::nil)))).

(*b ( 5 points)
Define the function "SortAList" that takes a nat list, and sorts the elements.
*)

Fixpoint Insert (n : nat) (l : list nat) :=
  match l with
    nil => n::nil |
    x::xs =>
      if blt_nat n x then n :: l
      else x::(Insert n xs)
  end.

Fixpoint SortAList (l : list nat) :=
  match l with
    nil => nil |
    x::xs => Insert x (SortAList xs)
  end.

Example SortEmptyList: SortAList nil = nil.
reflexivity.
Qed.

Eval simpl in (SortAList (4::2::1::5::2::3::7::6::nil)).

(*c (3 points)
Prove the following theorem:
Theorem List2c: forall (l : list nat), MaxOfAList l = MaxOfAList (SortAList l).
*)

Lemma blt_trans : forall (x y z : nat), ((blt_nat x y = true) /\ (blt_nat y z = true)) -> (blt_nat x z = true).
induction x.
intros.
destruct H.
destruct z.
destruct y.
simpl in H.
discriminate H.
simpl in H0.
discriminate H0.
reflexivity.
intros.
destruct H.
destruct y.
simpl in H.
discriminate H.
simpl in H.
destruct z.
simpl in H0.
discriminate H0.
simpl in H0.
simpl.
apply IHx with (y := y).
split.
assumption.
assumption.
Qed.


Lemma eq_succ : forall (n1 n2 : nat), (n1 = n2) -> (S n1) = (S n2).
intros.
rewrite H.
reflexivity.
Qed.

Lemma blt_eq: forall (n t : nat), ((blt_nat n t = false) /\ ( blt_nat t n = false)) -> (n = t).
induction n.
intros.
destruct H.
destruct t.
reflexivity.
simpl in H.
discriminate H.
intros.
destruct H.
destruct t.
simpl in H0.
discriminate H0.
simpl in H.
simpl in H0.
apply eq_succ.
apply IHn.
split.
assumption.
assumption.
Qed.

Lemma blt_false_true: forall (n t m : nat), ((blt_nat n t = false) /\ (blt_nat n m = true)) -> (blt_nat t m = true).
induction n.
intros.
destruct H.
destruct t.
destruct m.
discriminate H0.
assumption.
destruct m.
discriminate H0.
discriminate H.
intros.
destruct H.
destruct t.
destruct m.
discriminate H0.
reflexivity.
destruct m.
discriminate H0.
simpl in H.
simpl in H0.
simpl.
apply IHn.
split.
assumption.
assumption.
Qed.

Lemma blt_false_false : forall t n : nat, (((blt_nat n t) = false) /\ ((beq_nat n t) = false)) -> ((blt_nat t n) = true).
induction t.
intros.
destruct H.
destruct n.
discriminate H0.
reflexivity.
intros.
destruct H.
destruct n.
discriminate H.
simpl in H.
simpl in H0.
simpl.
apply IHt.
split.
assumption.
assumption.
Qed.

Lemma lem2c: forall (n : nat) (l : list nat), MaxOfAList (n::l) = MaxOfAList (Insert n l).
induction l.
reflexivity.
simpl.
remember (blt_nat a (MaxOfAList l)) as e1.
symmetry in Heqe1.
destruct e1.
remember (blt_nat n a) as e2.
symmetry in Heqe2.
destruct e2.
simpl.
assert (blt_nat n (MaxOfAList l) = true).
apply blt_trans with (y := a).
split.
assumption.
assumption.
rewrite Heqe1.
rewrite H.
reflexivity.
simpl.
rewrite <- IHl.
simpl.
remember (blt_nat n (MaxOfAList l)) as e3.
destruct e3.
rewrite Heqe1.
reflexivity.
remember (blt_nat a n) as e4.
destruct e4.
reflexivity.
symmetry in Heqe4.
apply blt_eq.
split.
assumption.
assumption.
remember (blt_nat n a) as e2.
destruct e2.
simpl.
rewrite Heqe1.
symmetry in Heqe2.
rewrite Heqe2.
reflexivity.
simpl.
rewrite <- IHl.
simpl.
remember (blt_nat n (MaxOfAList l)) as e3.
destruct e3.
rewrite Heqe1.
symmetry in Heqe1.
assert (blt_nat a (MaxOfAList l) = true).
apply blt_false_true with (n := n).
split.
symmetry.
assumption.
symmetry.
assumption.
rewrite H in Heqe1.
discriminate Heqe1.
remember (beq_nat n a) as e4.
symmetry in Heqe4.
destruct e4.
assert (n = a).
apply beq_nat_true.
assumption.
rewrite <- H.
destruct (blt_nat n n).
reflexivity.
reflexivity.
assert (blt_nat a n = true).
apply blt_false_false.
split.
symmetry.
assumption.
assumption.
rewrite H.
reflexivity.
Qed.

Theorem List2c: forall (l : list nat), MaxOfAList l = MaxOfAList (SortAList l).
induction l.
reflexivity.
simpl.
rewrite <- lem2c.
simpl.
rewrite <- IHl.
reflexivity.
Qed.



(***************************************************************************************
******************* I am a parting line, plz ignore me ******************************
***************************************************************************************)
Module Q5_7.
Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

Fixpoint app (l1 l2 : natlist) : natlist := 
  match l1 with
  | nil    => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y) 
                     (right associativity, at level 60).

Fixpoint snoc (l:natlist) (v:nat) : natlist := 
  match l with
  | nil    => [v]
  | h :: t => h :: (snoc t v)
  end.

Fixpoint rev (l:natlist) : natlist := 
  match l with
  | nil    => nil
  | h :: t => snoc (rev t) h
  end.




(***   Problem 5: More on Lists in Coq  (10 points)********************************)
Lemma rev_snoc: forall (n : nat) (l : natlist), rev (snoc l n) = n :: rev l.
Proof. 
intros. 
induction l.
simpl; reflexivity. 
simpl; rewrite -> IHl.
simpl; reflexivity.
Qed. 

Lemma rev_rev: forall (l : natlist), rev (rev l) = l.
Proof.
intros. 
induction l.
simpl; reflexivity.
simpl; rewrite -> rev_snoc.
rewrite -> IHl.
reflexivity.
Qed.

Theorem rev_inj : forall (l1 l2 : natlist), rev l1 = rev l2 -> l1 = l2.
Proof.
intros. 
rewrite <- (rev_rev l1). 
rewrite <- (rev_rev l2).
rewrite <- H. 
reflexivity.
Qed.



(***************************************************************************************
******************* I am a parting line, plz ignore me ******************************
***************************************************************************************)

(***   Problem 6: Inductive Definitions and double induction********************)

(*a (3 points)
A D3 tree is a data structure where each node has a value with a certain type,
 and each node has zero to (at most) three children. For example, here is a D3
tree with natural numbers as the values of nodes:

                                          ( 1 )
                                        /        \
                                      ( 2 )    ( 3 )
                                     /   |   \
                              ( 4 )  ( 5 )  ( 6 )
                                         |
                                       ( 7 )

Complete the definition of the D3 trees.*) 
Inductive d3tree {X : Type} : Type :=
| t_leaf : X -> d3tree
| t_one : X -> d3tree -> d3tree| t_two : X -> d3tree -> d3tree -> d3tree| t_three : X -> d3tree -> d3tree -> d3tree -> d3tree.

(* b (4 points)
Consider the following inductive definition for the Even and Odd predicates:
*)

Inductive even_old : nat -> Prop :=
  | even_O : even_old 0
  | even_S : forall n, odd_old n -> even_old (S n)
with odd_old : nat -> Prop :=
    odd_S : forall n, even_old n -> odd_old (S n).

(*Rewrite it into two polymorphical inductive definitions (named as
Even_new, and Odd_new), where,
for the one of Even, do not use Odd,and, for the one of Odd, do not use
Even.*)

Inductive Even_new: nat -> Prop :=| Even_base : Even_new O| Even_step : forall n,  Even_new n -> Even_new (S (S n)). 


Inductive Odd_new : nat -> Prop :=| Odd_base : Odd_new 1| Odd_step : forall n,  Odd_new n -> Odd_new (S (S n)).


(* c (3 points)
Prove the following theorem. (Hint: you may need to do double induction.
Also, consider about using keyword "inversion".)
Theorem Even_Odd_False: forall n, Even_new n -> Odd_new n -> False.
*)

Theorem Even_Odd_False: forall n, Even_new n -> Odd_new n -> False.
Proof.
induction 1.
(* equal to doing
intro.
intro.
induction n.
*)

(*Inversion ident
Let the type of ident  in the local context be (I t), where I is a (co)inductive 
predicate. Then, Inversion applied to ident  derives for each possible c
onstructor ci of (I t), all the necessary conditions that should hold for 
the instance (I t) to be proved by ci.*)

(* inversion num
This does the same thing as intros until num then inversion ident where 
ident is the identifier for the last introduced hypothesis.
*)
inversion 1.
inversion 1.
apply IHEven_new.
assumption.
Qed.



(***************************************************************************************
******************* I am a parting line, plz ignore me ******************************
***************************************************************************************)

(***** Some definitions on bags, as we saw in class *****)

Definition bag := natlist.

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.

Fixpoint count (v:nat) (s:bag) : nat := 
  match s with
    nil => 0
  | h :: t => if (beq_nat h v) then S (count v t)
                               else count v t
  end.


Fixpoint remove_one (v:nat) (s:bag) : bag :=
  match s with
    nil => nil
  | h::t => if (beq_nat v h)
             then t
             else h::(remove_one v t)
  end.






(***       Problem 7: Bags in Coq  (10 points )***************************************)

(*a*)
Theorem count_member_nonzero : forall (s : bag),
  ble_nat 1 (count 1 (1 :: s)) = true.
Proof.
intros. reflexivity.
Qed.

(** The following lemma about [ble_nat] might help you in the next proof. *)

Theorem ble_n_Sn : forall n,
  ble_nat n (S n) = true.
Proof.
intros n. 
induction n as [| n'].
simpl;  reflexivity.
simpl.  rewrite IHn'.  reflexivity.  Qed.

(*b*) 
Theorem remove_decreases_count: forall (s : bag),
  ble_nat (count 0 (remove_one 0 s)) (count 0 s) = true.
Proof.
  intros. induction s as [| s'].
  reflexivity. destruct s'.
  simpl. rewrite ble_n_Sn. reflexivity.
  simpl. rewrite IHs. reflexivity.
Qed.
End Q5_7.


(***************************************************************************************
******************* I am a parting line, plz ignore me ******************************
***************************************************************************************)

(***   Problem 8: Alternative Implementations of Stacks and Queues. (30 points)*****)
Module Q8.
(* a (6 points)
Implement a stack and a queue of natural numbers using a natlist, i.e.
define stack and queue each as a natlist and give definitions for an empty
stack/queue, and the operations for push/pop, enqueue/dequeue using
operations on natlists.

Assuming that (snoc (l:natlist) (n:nat)) is constant time, the operations for
push, pop, enqueue, dequeue should be constant time. You don't have to prove it.
*)



Notation "[ ]" := nil : list_scope.
Notation "[ a ; .. ; b ]" := (a :: .. (b :: []) ..) : list_scope.

Definition natlist : Type := list nat.

Fixpoint snoc (l:natlist) (v:nat) : natlist := 
  match l with
  | nil    => [v]
  | h :: t => h :: (snoc t v)
  end.

Hypothesis length_snoc : forall n : nat, forall l : natlist,
  length (snoc l n) = S (length l).


Definition natoption : Type := option nat.

Locate "*".

(** Define head with natoptions **)
Definition head (l : natlist) : natoption :=
  match l with
    [] => None
  | n :: l' => Some n
  end.

Definition stack := natlist.
Check stack.

Definition emptyS : natlist := nil.
Definition push (n:nat) (s : stack) := n::s.
Definition pop (s:stack) : (stack * natoption) :=
  (tail s, head s).

Definition queue := natlist.

Definition emptyQ : natlist := nil.
Definition enqueue (n:nat) (q:queue) := q ++ [n].
Definition dequeue (q:queue) : queue * natoption :=
  (tail q, head q).


(* b (7 points)
Give an alternative implementation of a queue of natural numbers using two stacks.
That is, redefine a queue as a pair of stacks and reimplement enqueue/dequeue
using only push and pop as the primary stack operations.

To remind you of the mechanism of using two stacks, enqueues correspond to
pushing to the first stack and dequeues correspond to popping from the second stack.
For a dequeue, when the second stack is empty, the contents of the first stack
are transferred to the second stack in reverse order, using only push and pop operations.
This results in an empty first stack. Finally the second stack is popped.

You are welcome to use any variant of the above implementation you are aware of.
*)

Fixpoint reverseAux (s1 s2 : stack) (l : nat) : (stack * stack) :=
  match pop s1 with
    (_, None) => (s1, s2)
  | (s1', Some n) =>
    match l with
      0 => (s1, s2) (** unreachable **)
    | S l' => reverseAux s1' (push n s2) l'
    end
  end.

Definition reverse (s : stack) : stack :=
  snd (reverseAux s emptyS (length s)).

Eval compute in (reverse (1::2::3::nil)).

Definition queue' : Type  := prod stack stack.
Check queue'.
Definition enqueue' (n:nat) (q: queue') := (push n (fst q), snd q).


Definition dequeue' (q:queue') : (queue' * natoption) :=
  match q with
    (nil, nil) => ((nil, nil), None)
  | (s1, nil) => let (s, no) := pop (reverse s1) in ((nil, s), no)
  | (s1, s2) => let (s, no) := pop (s2) in ((s1, s), no)
 end.


(* c (7 points)
For a queue implemented using a natlist, the corresponding natlist is the list of
numbers in the queue. Define a function which takes the queue implemented with
two stacks in part b above and returns a list of numbers corresponding to the queue.
*)

Definition listQ (q : queue') : natlist := snd q ++ reverse (fst q).





(* d (10 points)
Let q1 be a queue of the first implementation and q2 be a queue of the second
implementation. Let l(q) denote the list of numbers corresponding to the queue q
in either of these implementations.

Formulate and prove that if l(q1) = l(q2), l(enqueue(q1,n)) = l(enqueue(q2,n)) for any
natural number n and l(dequeue(q1)) = l(dequeue(q2)). Of course, use the notation
and terminology you defined previously for l(.), enqueue(.) and dequeue(.).

The tactics `compute' and `assert' might be useful. Also, you will get most of
the points if you make reasonable and intuitive assertions about list properties
and use them without proving if it is too time consuming.
*)

Lemma reverseAux_aux : forall (s1 s2 : stack) (a : nat),
  reverseAux (a::s1) s2 (length (a::s1)) = reverseAux s1 (a::s2) (length s1).
Proof. simpl. unfold push. reflexivity. Qed.

Lemma reverseAux_rev : forall (s1 s2 :stack),
  snd (reverseAux s1 s2 (length s1)) = rev s1 ++ s2.
Proof. induction s1.
reflexivity.
intro. rewrite reverseAux_aux. rewrite IHs1 with (s2:=a::s2).
simpl. rewrite <- app_assoc. simpl. reflexivity.
Qed.

Lemma reverse_rev : forall (s:stack), reverse s = rev s.
Proof. unfold reverse.
intro. rewrite reverseAux_rev. rewrite app_nil_r.
reflexivity.
Qed.

Theorem queue_stack_enqueue : forall (q1 : queue) (q2 : queue') (n:nat),
  q1 = listQ q2 -> enqueue n q1 = listQ (enqueue' n q2).
Proof. destruct q2. unfold enqueue.
unfold enqueue'. simpl. unfold listQ.
simpl. unfold push. rewrite reverse_rev.
intros. rewrite reverse_rev. simpl. rewrite H.
rewrite app_assoc. reflexivity.
Qed.

Lemma dequeue'_aux : forall (s1 s2 : stack) (n: nat),
  dequeue' (s1, n::s2) = ((s1,s2), Some n).
Proof. destruct s1. simpl. reflexivity.
simpl. reflexivity. Qed.

Theorem queue_stack_dequeue : forall (q1:queue) (q2: queue'),
  q1 = listQ q2  -> fst (dequeue q1)  = listQ (fst (dequeue' q2)).

Proof. destruct q2.
destruct s0.
destruct s.

simpl. unfold listQ. rewrite reverse_rev. rewrite reverse_rev.
simpl. intro. rewrite H. simpl. reflexivity.

unfold listQ. intro. simpl in H.
unfold dequeue'. simpl. rewrite H.
assert (reverse [] = []). rewrite reverse_rev. simpl. reflexivity.
rewrite H0. rewrite app_nil_r. reflexivity.

intro. unfold listQ in H. simpl in H.
assert (tail q1 = s0 ++ reverse s).
rewrite H. simpl. reflexivity.
unfold dequeue. simpl (fst (tail q1, head q1)).
rewrite H0. rewrite dequeue'_aux. simpl. unfold listQ. simpl.
reflexivity.
Qed. 

End Q8.


(***************** Congs! You have reached the end of the midterm exam! *********)





