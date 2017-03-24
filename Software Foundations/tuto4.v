Notation "x :: l" := (cons x l) 
        (at level 60, right associativity).
        
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint snoc (l:list nat) (v:nat) : list nat :=
  match l with
  | nil => [v]
  | h :: t => h :: (snoc t v)
  end.
  
Fixpoint rev (l:list nat) : list nat :=
  match l with
  | nil => nil
  | h :: t => snoc (rev t) h
  end.

Example test_rev1: rev [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.

Fixpoint beq_nat (m n : nat) :=
  match m with
  | O => match n with
         | O => true
         | S _ => false
         end
  | S m' => match n with
            | O => false
            | S n' => beq_nat m' n'
            end
  end.


Fixpoint index (n:nat) (l:list nat) : option nat :=
  match l with
  | nil => None
  | a :: l' => if beq_nat n O then Some a else index (pred n) l'
  end.

Example test_index1: index 3 [2;4;6;7;2;3;5;1] = Some 7.
Proof. reflexivity. Qed.
