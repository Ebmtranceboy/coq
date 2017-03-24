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

[Fill your answer in here. ]

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
(*Complete here*)
Admitted.

(* 2 points *)
Theorem bb : forall A B C: Prop, ((A /\ ~B -> C) /\ ~C ) /\ A -> B.
Proof.
(*Complete here*)
Admitted.

(* 3 points *)
Theorem bc : forall A B C D: Prop, (A -> B) -> ((C -> D) -> (A /\ C -> B /\ D)).
Proof.
(*Complete here*)
Admitted.

(* 3 points *)
Theorem bd:
forall (X : Set) (P : X -> Prop), ~(forall x, ~(P x)) -> (exists x, P x).
Proof.
(*Complete here*)
Admitted.

(***************************************************************************************
******************* I am a parting line, plz ignore me ******************************
***************************************************************************************)

(***** Some definitions/notations for lists, as we saw in class *****)

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


(***     Problem 3: Lists in Coq (10 points )******************************************
Define the following operations on Lists. Please remeber to demonstrate
your definition is correct. (Hint: you may need to define extra
functions in order to complete the functions that you are requested.)
***************************************************************************************)

(*a (3 points)
Define the function "IsElem" that checks whether an element belongs to a nat
list.
*)

(*Complete here*)

(*b (3 points)
Define the function "DropDupElem" that, given a nat list, eleminates
extra copies
of all duplicated elements. For instance, given [2, 4, 2, 3, 5, 3, 5,
5], it should
return a list only contains one 2, one 4, one 3, and one 5. Notice that, there
is no constraint on the order of elements in the returned list.
*)

(*Complete here*)

(*c (4 points)
Recall the definition of IsElem in the previous subproblem.
Prove the following theorem:
Theorem List1c : forall (n : nat) (l : list nat), IsElem n
(DropDupElem l) = IsElem n l. *)


(*Complete here*)



(***************************************************************************************
******************* I am a parting line, plz ignore me ******************************
***************************************************************************************)

(***   Problem 4: Play with Lists in Coq  (10 points)********************************)

(*a (2 points)
Define the function "MaxOfAList" that returns the maximal natural number in the
given nat list l. When l is empty, you can return 0. Please remeber to
demonstrate
your definition is correct. *)

(*Complete here*)

(*b ( 5 points)
Define the function "SortAList" that takes a nat list, and sorts the elements.
*)

(*Complete here*)

(*c (3 points)
Prove the following theorem:
Theorem List2c: forall (l : list nat), MaxOfAList l = MaxOfAList (SortAList l).
*)

(*Complete here*)



(***************************************************************************************
******************* I am a parting line, plz ignore me ******************************
***************************************************************************************)


(***   Problem 5: More on Lists in Coq  (10 points)********************************)
Theorem rev_inj : forall (l1 l2 : natlist), rev l1 = rev l2 -> l1 = l2.
Proof.
  (* FILL IN HERE *) Admitted.


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
(*Complete here*)
Admitted.

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

(*Complete here*)

(* c (3 points)
Prove the following theorem. (Hint: you may need to do double induction.
Also, consider about using keyword "inversion".)
Theorem Even_Odd_False: forall n, Even_new n -> Odd_new n -> False.
*)

(*Complete here*)



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
  (* FILL IN HERE *) Admitted.

(** The following lemma about [ble_nat] might help you in the next proof. *)

Theorem ble_n_Sn : forall n,
  ble_nat n (S n) = true.
Proof.
  intros n. induction n as [| n'].
    simpl.  reflexivity.
    simpl.  rewrite IHn'.  reflexivity.  Qed.

(*b*) 
Theorem remove_decreases_count: forall (s : bag),
  ble_nat (count 0 (remove_one 0 s)) (count 0 s) = true.
Proof.
  (* FILL IN HERE *) Admitted.



(***************************************************************************************
******************* I am a parting line, plz ignore me ******************************
***************************************************************************************)

(***   Problem 8: Alternative Implementations of Stacks and Queues. (30 points)*****)

(* a (6 points)
Implement a stack and a queue of natural numbers using a natlist, i.e.
define stack and queue each as a natlist and give definitions for an empty
stack/queue, and the operations for push/pop, enqueue/dequeue using
operations on natlists.

Assuming that (snoc (l:natlist) (n:nat)) is constant time, the operations for
push, pop, enqueue, dequeue should be constant time. You don't have to prove it.
*)


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


(* c (7 points)
For a queue implemented using a natlist, the corresponding natlist is the list of
numbers in the queue. Define a function which takes the queue implemented with
two stacks in part b above and returns a list of numbers corresponding to the queue.
*)


(* d (10 points)
Let q1 be a queue of the first implementation and q2 be a queue of the second
implementation. Let l(q) denote the list of numbers corresponding to the queue q
in either of these implementations.

Formulate and prove that if l(q1) = l(q2), l(enqueue(q1,n)) = l(enqueue(q2,n)) for any
natural number n and l(dequeue(q1)) = l(dequeue(q2)). Of course, use the notation
and terminology you defined previously for l(.), enqueue(.) and dequeue(.).

The tactics 'compute' and 'assert' might be useful. Also, you will get most of
the points if you make reasonable and intuitive assertions about list properties
and use them without proving if it is too time consuming.
*)




(***************** Congs! You have reached the end of the midterm exam! *********)





