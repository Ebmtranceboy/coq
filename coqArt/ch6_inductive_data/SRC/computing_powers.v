(** To put in a chapter about inductive types *)

(** Multiplication Schemes (CPS) *)

Require Import bin_nums tutorial_type_classes.SRC.Monoid Omega List.
Generalizable Variables op one.
Inductive Computation {A:Type} : Type :=
| Return (a : A)
| Mult (x y : A) (k : A -> Computation).


Notation "z '<---'  x 'times' y ';' e2 " := (Mult x y  (fun z => e2))
                                              (right associativity, at level 60).


Definition chain := forall (A:Type), A -> @Computation A.

(*
Axiom suggestion so as to get a hand on complexity properties.

Inductive similar {A B:Type}: @Computation A -> @Computation B -> Prop :=
| S_return: forall (a:A) (b:B), similar (Return a) (Return b)
| Mult_return: forall kA kB a1 a2 b1 b2, (forall a b, similar (kA a) (kB b)) ->
                                         similar (Mult a1 a2 kA) (Mult b1 b2 kB).

Axiom free_chain:
  forall (c:chain) A B a b,
    similar (c A a) (c B b).
 *)

Inductive equiv {A B:Type}: list (A*B) -> @Computation A -> @Computation B -> Prop :=
| Ereturn: forall (x:A) (y:B) (l:list (A*B)),
    In (x,y) l -> equiv l (Return x) (Return y)
| Emult: forall (x1 y1:A) (x2 y2:B) (l:list (A*B))
                (kA:A-> @Computation A) (kB:B -> @Computation B),
    In (x1,x2) l -> In (y1,y2) l ->
    (forall (x':A) (y':B),equiv  ((x',y')::l) (kA x') (kB y')) ->
    equiv l (Mult x1 y1 kA) (Mult x2 y2 kB).

(*Inductive well_formed {A:Type}: @Computation A -> @Computation A -> Prop:=
| Wf_return: forall (x:A), equiv (Return x) (Return x)
| Wf_mult: forall (x1 y1:A)(kA kA': A->@Computation A),
    (forall a:A, well_formed (kA a) (kA' a))
      well_formed (Mult x1 y1 kA) (Mult x1 y1 kA').*)



Axiom parametric_equiv: forall c:chain, forall A B (a:A) (b:B),
      equiv ((a,b)::nil) (c A a) (c B b).

Fixpoint execute {A:Type} `{M:Monoid A op one}   (c : @Computation A) : A :=
  match c with Return x => x
          | Mult x y k => execute (k (op x  y))
  end.

Definition apply_chain (c: chain){A}`{M:Monoid A op one} (a:A) :=
  execute (c A a).

(** number of mutiplications *)

Fixpoint comp_complexity   (c : @Computation unit) : nat :=
  match c with
  | Mult _ _ k => S (comp_complexity (k tt))
  | _ => 0%nat
  end.


Definition complexity (c: chain) := comp_complexity (c _ tt).

Require Import ArithRing.
Instance NatPlus : Monoid  plus 0%nat.
split; intros; ring.
Qed.

Definition the_exponent (c:chain) :=
  apply_chain c (M:= NatPlus) 1%nat.



(** the exponent associated to a chain *)


(** computation of x ^ 3 *)

Example  C3 : chain :=
  fun {A:Type} (a : A) =>
    a2 <--- a times a ;
    a3 <--- a2 times a ;
    Return a3.

Compute complexity C3.

(** computation of x ^ 7 *)

Example C7 : chain  :=
  fun {A} (x:A) =>
    x2 <--- x times x ;
    x3 <--- x2 times x ;
    x6 <--- x3 times x3 ;
    x7 <--- x6 times x ;
    Return x7.

Remark C7_correct : forall A `{M: Monoid A op one} (x:A),
    apply_chain C7 x = op x (op x (op x (op x (op x (op x x))))).
Proof.
  intros ; cbn.   now repeat rewrite  <- dot_assoc.
Qed.


(** Scheme for computing a x ^ p  (p positive)
 *)

Fixpoint axp_scheme  p {A:Type} : A -> A -> @Computation A :=
  match p with
  | xH =>  (fun a x => y <--- a  times x ; Return y)
  | xO q => (fun a x => x2 <--- x times  x ; axp_scheme q a x2)
  | xI q => (fun a x => ax <--- a times x ;
             x2 <--- x times x ;
             axp_scheme q ax x2)
  end.


Definition Pos_pow_chain (p:positive) :=
  match p with xH => fun (A:Type) (x:A) => Return x
          | _ => fun (A:Type) (x:A) => axp_scheme (Pos.pred p) x x
  end.


Definition C11 :=  Pos_pow_chain 11%positive.

Compute apply_chain (M:=ZMult) C11 2%Z.


(*
 = fun (A : Type) (x0 : A) =>
       x1 <--- x0 times x0; (* x^2 *)
       x2 <--- x0 times x1; (* x^3 *)
       x3 <--- x1 times x1; (* x ^ 4 *)
       x4 <--- x3 times x3; (* x ^8 *)
       x5 <--- x2 times x4; Return x5
 *)

Definition C87 : chain := fun A (x:A) =>
                            x2 <--- x times x ;
                            x3 <--- x2 times x ;
                            x6 <--- x3 times x3 ;
                            x7 <--- x6 times x ;
                            x10 <--- x7 times x3 ;
                            x20 <--- x10 times x10 ;
                            x40 <--- x20 times x20 ;
                            x80 <--- x40 times x40 ;
                            x87 <--- x80 times x7 ;
                            Return x87.


Compute the_exponent C87.
Compute the_exponent C11.





Definition chain_correct (c : chain) (p:positive) :=
  forall A `(M:Monoid A op one) (a:A), apply_chain c  a  =
                                       power a  (Pos.to_nat p).

Definition correct_chain_generator (f : positive  ->chain ) :=
  forall p, chain_correct (f p) p.


(** JUSQU'ICI TOUT VA BIEN *)



(** Correctness of the binary method *)

Lemma L : forall p A `(M:Monoid A op one) (a:A) x,
    execute (axp_scheme p a x) = op a (power x (Pos.to_nat p)).
Proof.
  induction p.
  -   intros a x; simpl axp_scheme.
      replace (Pos.to_nat p~1) with (S (Pos.to_nat p + Pos.to_nat p)%nat).
      cbn.
      intros;rewrite IHp; rewrite power_of_square, <- power_x_plus.
      now rewrite dot_assoc.
      rewrite  Pnat.Pos2Nat.inj_xI;omega.
  - intros a x; simpl  axp_scheme.
    replace (Pos.to_nat p~0 ) with (Pos.to_nat p + Pos.to_nat p)%nat.
    intros; simpl;  rewrite IHp, power_of_square,  <- power_x_plus;   auto.
    rewrite  Pnat.Pos2Nat.inj_xO;omega.
  - simpl; intros; now rewrite  (one_right x).
Qed.




Lemma binary_correct : correct_chain_generator Pos_pow_chain.
Proof.
  intros n x.  intros; unfold apply_chain.
  destruct n.
  simpl.
  rewrite  L.
  f_equal.
  rewrite <- (sqr  (A:=x) M).
  rewrite power_of_power.
  f_equal.
  rewrite (mult_comm  (Pos.to_nat n) 2)%nat.
  replace (2* Pos.to_nat n)%nat with (Pos.to_nat n + Pos.to_nat n)%nat.
  SearchAbout Pos.iter_op.
  now rewrite ZL6.
  ring.
  - simpl.
    rewrite  L.
    rewrite Pos2Nat.inj_xO.
    SearchAbout Pos.pred_double.
    SearchAbout power.
    replace (op a (power a (Pos.to_nat (Pos.pred_double n)))) with
    (power a (S (Pos.to_nat (Pos.pred_double n)))).
    SearchRewrite (S (Pos.to_nat _)).
    f_equal.
    rewrite <- Pos2Nat.inj_succ.
    SearchRewrite (Pos.succ (Pos.pred_double _)).
    rewrite Pos.succ_pred_double.
    SearchRewrite (Pos.to_nat (xO _)).
    now rewrite Pos2Nat.inj_xO.
    now  simpl.
  - simpl.
    now rewrite one_right.
Qed.


(** We can define "optimal" algorithms for generating computation schemes *)

Definition optimal (f : positive -> chain) :=
  forall (g : positive  -> chain),
    correct_chain_generator  g ->
    forall p, (complexity (f p) <= complexity (g p))%nat.

(** In the following section, we show that the binary method is not optimal *)

Section bin_pow_scheme_not_optimal.

  Hypothesis binary_opt : optimal Pos_pow_chain.

  (** First, let's have a look at the computation scheme generated for, let's say, 87  *)
  Compute Pos_pow_chain 87.

  (*   The variables output by Coq have been renamed by hand
      (x_i associated with x ^ i)

 =
fun (A : Type) (x : x) =>
       x_2 <--- x times x;
       x_3 <--- x times x_2;
       x_4 <--- x_2 times x_2;
       x_7 <--- x_3 times x_4;
       x_8 <--- x_4 times x_4;
       x_16 <--- x_8 times x_8;
       x_23 <--- x_7 times x_16;
       x_32 <--- x_16 times x_16;
       x_64 <--- x_32 times x_32;
       x_87 <--- x_23 times x_64;
       Return x_87
     : forall A : Type, A -> Computation
   *)


  Compute complexity (Pos_pow_chain 87 ).

  Compute complexity C87.

  (** Notice that C87 has been automatically generated with the
   "euclidean addition chains" method


http://www-igm.univ-mlv.fr/~berstel/Articles/1994AdditionChains.pdf

https://eudml.org/doc/92517

   *)


  Lemma L87 : chain_correct C87 87.
  Proof.
    red.
    intros.
    compute.
    now repeat (rewrite dot_assoc || rewrite (one_right (Monoid :=M))).
  Qed.


  (** we slightly modify the binary scheme
   *)

  Definition h (p:positive) := if Pos.eqb p 87%positive
                               then C87
                               else Pos_pow_chain p.

  Lemma h_correct : correct_chain_generator h.
  Proof.
    intro p; case_eq (Pos.eqb p 87).
    -   intros H a;  unfold h;   rewrite H.
        rewrite   Pos.eqb_eq in H;  subst p; apply L87.
    -   intros ; unfold h;   rewrite H;   apply binary_correct.
  Qed.

  Lemma absurd : False.
  Proof.
    generalize (binary_opt h  h_correct 87%positive).
    compute;
      intros. omega.
  Qed.

End bin_pow_scheme_not_optimal.

(*** The computation scheme associated to naive power *)

(** In fact, the computation scheme for the naive algorithm is just
    the iteration of the following function *)

(*


Definition transform (f : (A -> Computation) -> (A -> Computation))
                     (k: A -> Computation) (x: A) :=
                     f (fun y:A => z <--- y times x ; k z) x.

Definition naive_power_scheme (i:N) :=
match i with 0 => fun x => Return one
          | Npos q => Pos.iter  transform (fun k => k) (Pos.pred q)
                                 Return
end.
 *)

Definition transform{A:Type}
           (f: (A -> @Computation A) -> (A -> @Computation A))
           (c : (A ->  @Computation A)) :  A -> @Computation A
  := fun (x:A) =>
       f (fun (y:A) => z <--- y times x ; c z) x.

Definition naive_power_scheme (i:positive) : chain :=
  fun (A: Type) =>
    Pos.iter  (transform (A:=A)) (fun k => k) (Pos.pred i)
              Return
.

Compute naive_power_scheme 6.
Compute the_exponent (naive_power_scheme 6).
