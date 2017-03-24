(*http://www.labri.fr/perso/casteran/CoqArt/newstuff/mergesort.html *)
(* An exercise from Epigram tutorial *)
(* Pierre Castéran, Julien Forest *)

Require Import List.
Require Import Wf_nat.
Require Import Recdef.
Require Import Compare_dec.
Require Import Arith.
Require Import Peano_dec.
Require Import Omega.
Require Import RelationClasses.
Import Relations.

Section Polymorphic_Sort.
Variables (A:Type)
          (le : relation A)
          (eq_dec : forall a b:A, {a = b} + {a <> b})
          (le_dec : forall a b: A, {le a b} + {le b a}).

Context (le_pre : PreOrder le).

Notation "a <= b" := (le a b).

(** Specification of a sorting function *)

(** being sorted w.r.t. le *)

Inductive sorted : list A -> Prop :=
  sorted_nil : sorted nil
| sorted_single : forall a, sorted (a::nil)
| sorted_cons : forall a b l, a <= b -> sorted (b::l) -> sorted (a::b::l).

Hint Constructors sorted.

(** number of occurrences of a in l 
*)

Fixpoint multiplicity (a:A)(l:list A){struct l}:nat :=
  match l with
  | nil => 0
  | b::l' => if eq_dec a b  then S (multiplicity a l') 
                               else multiplicity a l'
  end.


(**   (non-effective) definition of permutation *)
 
Definition permutation (l l':list A) :=
 forall a: A , multiplicity a l = multiplicity a l'.

(** Specification of any sorting function *)

Definition sort_rel (l l': list A) := 
  sorted l' /\ permutation l l'.

Definition sort_correct  (f: list A -> list A) : Prop :=
     forall l:list A, sort_rel l (f l).

(** Lemmas about sorted *)


Lemma sorted_single_cons: forall l , sorted l ->
                           forall x,
                           (forall y, In y l -> x <= y) ->
                           sorted (x::l).
Proof.
 induction l.
 -  intros;constructor.
 -  intros;constructor.
    generalize (H0 a); intro H1;apply H1;auto.
    + now constructor.
    + auto.
Qed.

Lemma sorted_trans : forall l a x, sorted (a::l) -> x <= a -> sorted (x::l).
Proof.
 inversion_clear 1.
 -  constructor.
 - intro; refine (sorted_cons _ _ _ _ H1).
   + now   transitivity a. 
Qed.

Lemma sorted_inv_In : forall l x, sorted (x::l) -> forall y, In y l -> x<=y. 
Proof.
 induction l.
 -  inversion 2.
 -  intros x H y H0; case  (in_inv H0). 
    + intro;subst y;inversion_clear H;auto.
    +   intros; eapply IHl;auto.
        inversion H;  apply sorted_trans with a;auto.
Qed.

(** Exercise 

  Can you  state and prove that for any list l, there exists at most
  one list l' such that l' is sorted and l' is a permutation of l ?

  Do you have to add some hypothesi/e/s to the current context? *)

(** Merging lists *)

(* merging a pair of lists *)

Function pair_merge (ls : list A * list A) 
         {measure  (fun ls => length (fst ls)+ length (snd ls))} : list A :=
 match ls with 
   (nil,nil) => nil
  | (nil,l ) | (l, nil) => l
  | (x1::l1,x2::l2) => if le_dec x1 x2 
                       then x1::(pair_merge(l1,x2::l2))
                      else  x2::(pair_merge(x1::l1,l2))
  end.
Proof.
 - simpl; auto with arith.
 - simpl;auto with arith.
Qed.
About pair_merge_rect.

(** pair_merge_rect :
pair_merge_rect :
forall P : list A * list A -> list A -> Type,
(forall ls : list A * list A, ls = (nil, nil) -> P (nil, nil) nil) ->
(forall (ls : list A * list A) (l : list A),
 ls = (nil, l) ->
 (let (l0, l1) := (nil, l) in
  match l0 with
  | nil => match l1 with
           | nil => False
           | _ :: _ => True
           end
  | _ :: _ => match l1 with
              | nil => False
              | _ :: _ => False
              end
  end) -> P (nil, l) l) ->
(forall (ls : list A * list A) (l : list A),
 ls = (l, nil) ->
 (let (l0, l1) := (l, nil) in
  match l0 with
  | nil => match l1 with
           | nil => False
           | _ :: _ => False
           end
  | _ :: _ => match l1 with
              | nil => True
              | _ :: _ => False
              end
  end) -> P (l, nil) l) ->
(forall (ls : list A * list A) (x1 : A) (l1 : list A) (x2 : A) (l2 : list A),
 ls = (x1 :: l1, x2 :: l2) ->
 forall _x : x1 <= x2,
 le_dec x1 x2 = left _x ->
 P (l1, x2 :: l2) (pair_merge (l1, x2 :: l2)) ->
 P (x1 :: l1, x2 :: l2) (x1 :: pair_merge (l1, x2 :: l2))) ->
(forall (ls : list A * list A) (x1 : A) (l1 : list A) (x2 : A) (l2 : list A),
 ls = (x1 :: l1, x2 :: l2) ->
 forall _x : x2 <= x1,
 le_dec x1 x2 = right _x ->
 P (x1 :: l1, l2) (pair_merge (x1 :: l1, l2)) ->
 P (x1 :: l1, x2 :: l2) (x2 :: pair_merge (x1 :: l1, l2))) ->
forall ls : list A * list A, P ls (pair_merge ls)
*)


Definition merge l1 l2 := pair_merge (l1,l2).





(* About merging  *)
 
Lemma In_merge_inv : forall (ls : list A * list A) (a:A),
                    In  a (pair_merge ls) -> In a (fst ls) \/ In a (snd ls).
Proof.
 intros ls a ;functional induction (pair_merge ls).
 - simpl; contradiction.
 -  right;simpl;auto.
 -  left;simpl;auto.
 -  intro H; case (in_inv H).
   +  intro;subst a;  left;simpl;auto.
   +  intro H1;case (IHl H1); simpl; auto.
 -    simpl in *. 
      destruct 1 as [H1 | H2];auto. 
     destruct (IHl H2); auto. 
Qed.
 

Lemma sorted_merge : forall ls, sorted (fst ls) -> sorted (snd ls) ->
                      sorted (pair_merge ls).
Proof.
 intros; functional induction (pair_merge ls).
 -   constructor.
 -  simpl in H0;auto.
 -  simpl in H;auto.
 -  simpl in *;  apply sorted_single_cons.
    +  apply IHl.
       inversion H;auto.
       assumption.
     +  intros y H1; case ( In_merge_inv _ _ H1); simpl.
       intros;eapply sorted_inv_In;eauto.
       destruct 1.  
      * subst y;auto.
      *  transitivity x2;  auto.
         eapply sorted_inv_In;eauto.
 -  simpl in *;  apply sorted_single_cons. 
    + apply IHl;auto.
      inversion_clear H0.
      constructor;auto.
      assumption.
 +  intros y H1;  case ( In_merge_inv _ _ H1).
    simpl; destruct 1.
     subst y.  assumption. 
      transitivity x1.    auto. 
    eapply sorted_inv_In with l1; auto.
   simpl.
      eapply sorted_inv_In;eauto.
Qed.

(**
   A  tree is balanced if every node has either the same number
 of leaves in both of its subtrees, or on more leaf in its 
  left subtree than its right subtree.

  The following data structures stores in in each node a boolean
  value for discriminating between the two cases above *)







(* First a fully polymorphic definition of binary trees:

(N,L) trees :
    binary trees whose leaves are labeled by L and nodes by N *)

Inductive tree(N L:Type):Type :=
  Leaf : L -> tree N L
| Node : N -> tree N L -> tree N L -> tree N L.

Arguments Leaf {N L} _.
Arguments Node {N L} _ _ _.

(** We use an option type for saying whether some leaf 
   bears a value of type A --- we say it's a "true" leaf --- or not *)

Let T := tree bool (option A).

(* number of "true"  leaves in a tree of type T *)

Fixpoint filled_leaves (t: T) : nat :=
 match t with
   Leaf  None => 0
   | Leaf  (Some a) => 1
   | Node _ t1 t2 => filled_leaves  t1 + filled_leaves t2
 end.



(**
A  tree is balanced if every node labeled with true has 
   the same number of real leaves in both subtrees, and every
   node labeled with false has one more real leave in its left son
   than its right son.
   
  The proposition (balanced n t) means that t is balanced and 
  has $n$ real leaves.
 *)


Inductive balanced: T -> nat -> Prop :=
  bal_none :  balanced    (Leaf None) 0
| bal_some : forall a, balanced (Leaf  (Some a)) 1
| bal_eq : forall t1 t2 n, balanced  t1 n -> balanced t2 n ->
                           balanced    (Node  true t1 t2)  (2 * n)
| bal_diff : forall t1 t2 n , balanced t1 (S n) ->
                              balanced   t2 n ->
                              balanced (Node false t1 t2) (S ( 2 * n)).



(** ** Building a tree from a list *)

(* insertion of a label in  a tree *)

Fixpoint insert (a:A)(t: T) {struct t} : T :=
  match t with 
    | Leaf None => Leaf  (Some a)
    | Leaf (Some b) => Node  true (Leaf  (Some b)) 
                             (Leaf (Some a))
    | Node  true  t1 t2 =>
      Node false (insert  a t1) t2
    | Node  false  t1 t2 =>
      Node  true t1  (insert a t2)
  end.

(* transforms a list into a tree *)

Fixpoint  share (l:list A)  {struct l}: T :=
  match l with
    | nil => Leaf  None
    | a::l' => insert a (share  l')
  end.


(** extraction of a label list from a tree *)

Fixpoint flatten (t: T) : list A :=
 match t with
   Leaf  None => nil
 | Leaf  (Some a) => a::nil
 | Node _  t1 t2 => merge (flatten t1) (flatten t2)
end.

Definition mergesort (l:list A):list A :=
  flatten (share  l).

(** Some properties of balanced trees *)

Lemma balanced_filled_leaves : forall t n, balanced   t n ->
                                           filled_leaves t = n.

  intros t; induction t. 
 -   (* first branch of filled_leaves *)
     inversion_clear 1;reflexivity.
 -   (* second branch of filled_leaves *)
      inversion_clear 1. simpl. rewrite (IHt1 _ H0), (IHt2 _ H1). omega.
      simpl. rewrite (IHt1 _ H0), (IHt2 _ H1). omega.
Qed.


Lemma balanced_inv_eq :
 forall  t1 t2 n, balanced   (Node true t1 t2) n ->
                 filled_leaves  t1 =  filled_leaves  t2.
Proof.
 inversion_clear 1.
 -  rewrite (balanced_filled_leaves _ _   H0),
            (balanced_filled_leaves  _ _ H1);
    auto.
Qed.



Lemma balanced_inv_diff :
 forall  t1 t2 n, balanced  (Node false t1 t2) n ->
                 filled_leaves  t1 =  S (filled_leaves  t2).
Proof.
 inversion_clear 1.
 rewrite (balanced_filled_leaves  _ _ H0),
         (balanced_filled_leaves  _ _ H1);auto.
Qed.

Function multiplicity_in_tree (a:A)(t:T){struct t} : nat:=
 match t with
 | Leaf  None => 0
 | Leaf   (Some b) => if eq_dec a b then 1 else 0
 | Node  _ t1 t2 =>   multiplicity_in_tree a t1 +   multiplicity_in_tree a t2
 end.  


(* lemmas about insert *)

Lemma insert_balanced : forall (a:A)(t: T) n,
        balanced   t n -> 
        balanced    (insert a t) (S n).
Proof.
  intros a t; induction t; simpl.
  -  inversion_clear 1. 
     + constructor.
     + change 2 with (2 * 1); repeat constructor.
  - inversion_clear 1.   
    + constructor;auto.
    + replace (S (S (2 * n1))) with (2 * (S n1)) by omega; constructor;auto.  
Qed.


Lemma share_balanced : forall (l:list A),
                        balanced  (share  l) (length l).
Proof.
  intros l; induction l; simpl. 
  - constructor. 
  -  now apply insert_balanced. 
Qed.



Lemma flatten_sorted : forall t, sorted (flatten t).
Proof.
  intros t; induction t;  simpl. 
  -   destruct l; constructor; auto.
  -  apply sorted_merge;simpl;assumption.
Qed.



(**********************
  This part shows that mergesort computes a permutation *)

Lemma multiplicity_insert : forall (t : T) n p, 
                    multiplicity_in_tree  p (insert  n t) =
                    if eq_dec p n 
                    then S (multiplicity_in_tree p t)
                    else multiplicity_in_tree p t.
Proof.
  intros t n; induction t; simpl; auto. 
  -   destruct l; simpl.
      intro p; case (eq_dec p a); case (eq_dec p n); intros; auto with arith.
      intro p; simpl.
  reflexivity.
  -  intro p; specialize (IHt1 p);specialize  (IHt2 p). 
     destruct (eq_dec p n).
     +  destruct n0;simpl in *.
      *   rewrite IHt1; ring.
      *   rewrite IHt2;ring.
     + destruct n0;simpl in *.
      * rewrite IHt1; ring.
      * rewrite IHt2;ring.
Qed.  


Lemma multiplicity_share : forall l n, multiplicity n l = multiplicity_in_tree n 
                                                  (share  l).
Proof.
  intros l; induction l; simpl. 
  -   reflexivity. 
  -   intro n;rewrite  multiplicity_insert.
      case (eq_dec n a); auto.
Qed.


Lemma merge_plus : forall n ls, multiplicity n (pair_merge ls) =
                                   multiplicity n (fst ls) + multiplicity n (snd ls).
Proof. 
 intros n ls;functional induction (pair_merge ls); simpl; auto.
 -   simpl in *; rewrite IHl; case (eq_dec n x1);  auto.
 -  simpl; case (eq_dec n x2).
    +  rewrite IHl; intro ;subst x2;simpl;auto.
    +  intro; case (eq_dec n x1).
       *  rewrite IHl; simpl;auto.
          intro;case (eq_dec n x1).
           simpl;auto.
           intro d;case d;trivial.
       * rewrite IHl;simpl.
         intro; case (eq_dec n x1).
         intro;case n1;auto.
         auto.
Qed.


Lemma flatten_multiplicity : forall t  n, multiplicity n (flatten t)=
                                      multiplicity_in_tree n t.
Proof.
  intros t; induction t; simpl. 
  -  destruct l; simpl;reflexivity.
  - intro n0. unfold merge; rewrite merge_plus. rewrite IHt1;rewrite IHt2;auto.
Qed.

Lemma merge_of_append : forall l l',
                        permutation (l ++ l') (merge l l').
Proof.
 red; unfold merge; intros;rewrite  merge_plus; simpl.
 generalize l';induction l;simpl; auto.
 case (eq_dec a a0).
 -  intros;rewrite IHl;auto.
 - auto.
Qed.

Lemma merge_and_sort : forall l l', sorted l -> sorted l' ->
                                    sort_rel (l++l') (merge l l').
Proof.
 split.
 -  unfold merge;apply sorted_merge;auto.
 -  apply merge_of_append.
Qed.

 


Theorem mergesort_permut : forall l , permutation l  (mergesort l).
Proof.
 intros;red;intros;unfold mergesort;rewrite (multiplicity_share l).
  now rewrite flatten_multiplicity.
Qed.


Theorem mergesort_ok : sort_correct mergesort.
Proof.
 red; intro l;split.
 - unfold mergesort; apply flatten_sorted.
 -  apply mergesort_permut.
Qed.


End Polymorphic_Sort.

(** Tests :
About mergesort.

Recursive Extraction mergesort.

*)
