Module prop.
Check nat.
Check bool.
Check (2+2) = 5.

Definition true_for_zero (P : nat -> Prop) : Prop := P 0. 
Definition preserved_by_S (P : nat -> Prop)  : Prop := 
  forall n : nat, P n -> P (S n).
Definition true_for_all_numbers (P : nat -> Prop) :=
  forall n : nat, P n.
Definition our_nat_induction (P : nat -> Prop) :=
  (true_for_zero P) -> (preserved_by_S P) -> (true_for_all_numbers P).
  
Definition tautology : Prop :=
  forall P : Prop, P -> P.
Theorem proof_tautology : tautology.
Proof.
 intros P H. assumption. Qed.

Theorem mult_0_r'' : forall n:nat,
  n*0 = 0.
Proof. 
  apply nat_ind. reflexivity.
  simpl. intros n' IHn'. apply IHn'. Qed.

Check negb.
Check andb.
Theorem invers_andb : forall a b : bool,
  andb a b = true -> a = b.
Proof. 
  intros a b H.
  destruct a.
  destruct b. reflexivity. discriminate.
  destruct b. discriminate. reflexivity. Qed. 


End prop.