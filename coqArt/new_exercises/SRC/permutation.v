(************************************************************************)
(*                            Houda ANOUN                               *)
(*                            2004 -2005                                *)
(*                        About List Permutation                        *)
(*                              LaBRI                                   *)
(************************************************************************)
Require Export List.
Require Export Arith.
Require Export Omega.
Require Export RelationClasses.
Import Relations.


Set Implicit Arguments.


Section perm.
(** Let us consider some type with decidable equality *)

Variables (A : Type)
         (A_eq_dec : forall a b : A, {a = b} + {a <> b}).

(* some additional lemmas and definitions about lists *)
 
(**  insertion of a at any place in a list *)

 Inductive insert(a:A):list A ->list A->Prop:=
 |insert_fst:forall (l1 :list A), insert a l1 (a::l1)
 |insert_rest :forall l1 l2 b, insert a l1 l2 ->
                               insert a (b::l1) (b::l2).



 Lemma insert_in:forall (l1:list A)a,
                    In a l1->
                    exists l2, insert a l2 l1.
 Proof.
  intros l1; induction l1 as [ | a l1 IHl1].
  -  simpl in |- *; tauto.
  -  simpl in |- *.
  intros a0 H0; case H0.
  +  intro; subst; exists l1; constructor.
  +   intro H1; destruct (IHl1 _ H1) as [x Hx].
          exists (a::x);  now constructor 2.  
 Qed.


(***********************************************************************)
(*      (Yet Another) Inductive definition of list permutation         *)
(***********************************************************************)


Inductive permI  :list A ->list A ->Prop:=
|permI_refl:forall l, permI l l
|permI_cons:forall a l0 l1, permI l0 l1-> permI (a::l0)(a::l1)
|permI_app:forall a l, permI (a::l) (l++(a::nil))
|permI_trans:forall l1 l2 l3,
              permI l1 l2 -> permI l2 l3 -> permI l1 l3.


Lemma permI_app_com:forall (l1 l2:list A),
                      permI (l1++l2)(l2++l1).
Proof.
 intro l1; elim l1.
 - simpl in |- *.
   intro; rewrite <- app_nil_end; constructor.
 - intros a l IHl l2.
   econstructor 4;   simpl in |- *.
   constructor 3.
   rewrite app_ass.
   replace (l2 ++ a :: l) with ((l2 ++ a :: nil) ++ l); auto.
   rewrite app_ass.
   reflexivity.
Qed.

Instance permI_sym: Symmetric permI. 
Proof.
 red; induction 1.
 -  constructor.
 -  constructor; auto.
 - replace (a :: l) with ((a :: nil) ++ l).
   apply permI_app_com; constructor.
   simpl in |- *; auto.
 - econstructor 4; eauto.
Qed.

Lemma permI_insert:forall (l1 l2:list A)a,
                   insert a l1 l2->
                   permI (a::l1) l2.
Proof.
 induction 1.
 -  constructor.
 - econstructor 4.
  +  econstructor 3.
  +  simpl in |- *; constructor.
     constructor 4 with (a :: l1).
     * symmetry; constructor.
     * assumption.
Qed.

(***************************************************)
(*   properties about permutation (with multisets) *)
(***************************************************)


Fixpoint multiplicity (a:A) (l:list A) : nat:=
  match l with nil => 0
             | b::l' => ((if A_eq_dec a b then 1 else 0) + 
                        multiplicity a l')
 end.

Definition permutation (l1 l2:list A):Prop :=
 forall a, multiplicity a l1 = multiplicity a l2.

Lemma multiplicity_of_append:forall a (l1 l2:list A),
   multiplicity a (l1 ++ l2) = 
   multiplicity a l1 + multiplicity a l2.
Proof.
 intro a; induction l1;simpl;auto.
 intro l2;rewrite IHl1; omega.
Qed.

Lemma permutation_cons : forall a l1 l2, permutation l1 l2 ->
                                         permutation (a::l1) (a::l2).
Proof.
 unfold permutation;intros a l1 l2 H a0; simpl;
 case_eq ( A_eq_dec a0 a);rewrite (H a0);auto.
Qed.


Instance permutation_trans : Transitive permutation.
Proof.
 red; unfold permutation;intros x y z H H0 a; rewrite H;auto.
Qed.


Lemma permutation_of_nil:forall (l:list A),
               permutation  nil l->
               l=nil.
Proof.
 unfold permutation;simpl.
 intro l; case l;auto.
 intros a l0 H; generalize (H a).
 unfold multiplicity;case_eq(A_eq_dec a a).
 - intros;elimtype False;    omega. 
 - intro n;destruct n;auto.
Qed.


Lemma multiplicity_positive:forall a (l:list A),
             multiplicity a l >=1 ->
             In a l.
Proof.
 induction l;simpl.
 -  omega.
 -  case_eq (A_eq_dec a a0);simpl.
    +  intro e;subst a0;auto.
    +  intros _ _ H;right;auto.
Qed.
 
Lemma multiplicity_insert_eq:forall a (l1 l2:list A),
                    insert a l1 l2->
                   multiplicity a l2 = 
                   S (multiplicity a l1).
Proof.
 induction 1.
 -  simpl in |- *.
    case (A_eq_dec a a).
    +  intro; omega.
    +  destruct 1;trivial.
 - simpl;rewrite IHinsert; omega.
Qed.

Lemma multiplicity_insert_diff:forall a a0 (l1 l2:list A),
                    insert a l1 l2->
                    a<>a0->
                   multiplicity a0 l2 =
                   multiplicity a0 l1.
Proof.
 induction 1;simpl.
 -  case_eq (A_eq_dec a0 a).
  +  intros H _ H';destruct H';auto.
  +  intros n e _; simpl;auto.
 - intro; rewrite IHinsert;auto.
Qed.

Lemma permutation_of_insert:forall a (l1 l2 :list A),
         insert a l1 l2 ->
       forall l3 ,  
          permutation  (a::l3) l2->
          permutation  l3 l1.
Proof.
 unfold permutation; simpl.
 intros a l1 l2 H l3 H0 a0; pose (H0 a0).
 generalize e; clear e; case_eq (A_eq_dec a0 a).
 -  intros H1 H2; subst; rewrite (multiplicity_insert_eq H); 
    intros;omega.
 - intros; rewrite <- (multiplicity_insert_diff H ); auto.
Qed.


(************************************************)
(*   equivalence  between the two definitions   *)
(************************************************)


Theorem perm_inductive_mset : forall (l1 l2:list A),
                   permI l1 l2 ->
                   permutation  l1 l2.
Proof.
 induction 1.
 -  red;auto.
 - apply permutation_cons; auto.
 - unfold permutation in *;  simpl ; intros; rewrite multiplicity_of_append.
   simpl in |- *; omega.
 -  eapply permutation_trans; eauto.
Qed.



(* from multiset definition to inductive definition *)

Theorem permutation_permI : forall (l1 l2:list A),
                   permutation l1 l2->
                    permI l1 l2.
Proof.
 intro l1; elim l1.
 -  intros l2 H; rewrite (permutation_of_nil H); constructor.
 -  intros a l H l2 H0; assert (In a l2).
  +  apply multiplicity_positive.
     unfold permutation in H0.
     simpl in H0.
     rewrite <- (H0 a).
     case (A_eq_dec a a).
    *  intro; omega.
    *  induction 1; auto.
  +  elim (insert_in _ _ H1).
    intros x Hx; constructor 4 with (a :: x).
    * constructor.
      apply H.
      eapply permutation_of_insert.
      eauto.
      auto.  
    *  apply permI_insert; auto.
Qed.

End perm.



Lemma counterexample : ~ permI (2::3::5::5::8::7::4::nil) 
                               (3::2::8::7::4::3::5::nil).
 red;intro.
 generalize (perm_inductive_mset eq_nat_dec H).
 intro H0.
 generalize (H0 3).
 discriminate 1. 
Qed.




