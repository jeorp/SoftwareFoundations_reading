Module poly.
Require Import Arith.
Check nat.

Theorem eq_add_S : forall n m : nat,
  S n = S m -> n = m.
Proof.
  intros n m eq. inversion eq. reflexivity. Qed.

Theorem silly6 : forall (n : nat),
     S n = O ->
     2 + 2 = 5.
Proof.
  intros n contra. inversion contra. Qed.

Theorem plus_n_Sm : forall n m : nat,
  n + (S m) = S (n + m).
Proof.
  intros n m.
  induction n as [| n']. simpl. reflexivity.
  simpl. rewrite -> IHn'. reflexivity. Qed.

 

  
  
  
  

End Poly.
