(* unordered pairs  *)

Require Import DecidableType.
Require Import DecidableTypeEx.

Module Upair (M: DecidableType)  <: DecidableType 
with  Definition t := (M.t * M.t)%type.

Definition t := (M.t * M.t)%type.


Definition eq(p p':t) : Prop :=
  let (x,y) := p in
  let (x',y') := p' in
       M.eq x x' /\ M.eq y y' \/
       M.eq x y' /\ M.eq y x'.


Lemma  eq_refl : forall x : t, eq x x.
Proof.
  destruct x ;left;simpl;auto.
Qed.

Lemma  eq_sym : forall x y : t, eq x y -> eq y x.
Proof.
 intros (x0,x1) (y0,y1) [(H1,H2)|(H1,H2)]; simpl in H1,H2;
 [left|right];split;auto.
Qed.
 
 
Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
Proof.
 intros (x0,x1) (y0,y1) (z0,z1) [(H1,H2)|(H1,H2)] [(H3,H4)|(H3,H4)];
 simpl in * ;
 [left|right|right|left];eauto.
Qed.


Definition eq_dec :forall x y : t, { eq x y } + { ~ eq x y }.
Proof.
 destruct x as (t0, t1);destruct y as (t2,t3).
 case (M.eq_dec t0 t2).
 - intro e; case (M.eq_dec t1 t3).
   +  left;red; left; simpl;auto. 
   +  intro n; right;red.
      intros [(H1,H2)|(H1,H2)];simpl in *.
      contradiction H2.  
      destruct n.   
      apply M.eq_trans with t2;auto.
      apply M.eq_trans with t0;auto.
  -  intro n.
     case (M.eq_dec t0 t3);intro H.
     +  case (M.eq_dec t1 t2);intro H1.
        *  left; right;simpl; auto.
        *  right; intros [(H2,H3)|(H2,H3)]; simpl in *; firstorder.
     +  right; intros [(H2,H3)|(H2,H3)]; simpl in *; firstorder.

Defined.

End Upair.

(**  example 

*)
Require Import ZArith.

Module Zpair := Upair Z_as_DT.
Recursive Extraction Zpair.eq_dec.
Open Scope Z_scope.

Lemma test :
 is_true (if Zpair.eq_dec  (5,6) (4+2,5) then true else false).
Proof. reflexivity. Qed.


