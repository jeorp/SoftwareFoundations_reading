Module nat3.

Check nat.
Check bool.

Theorem plus_0_n : forall n: nat, 0+n=n.
Proof.
  intros n. reflexivity. Qed.
Theorem plus_1_n : forall n:nat, 1+n=S n.
Proof.
  intros n. simpl. reflexivity. Qed.
Theorem mult_0_n: forall n:nat, 0*n=0.
Proof.
 intros n. reflexivity. Qed.
Theorem plus_id_example: forall n m: nat,
  n=m -> n+n=m+m.
Proof.
  intros n m H. rewrite -> H. reflexivity. Qed.
Theorem plus_id_exercise : forall n m o:nat,
  n=m -> m= o -> n+m=m+o.
Proof.
  intros n m o.
  intros H H0.
  rewrite->H.
  rewrite->H0.
  reflexivity.
  Qed. 
Theorem mult_0_plus: forall n m:nat,(0+n)*m=n*m.
Proof.
  intros n m.
  rewrite -> plus_0_n.
  reflexivity.
  Qed.
Theorem mult_1_plus: forall n m:nat,(1+n)*m=m+n*m.
Proof.
  intros n m.
  rewrite -> plus_1_n.
  reflexivity.
  Qed.  
Theorem plus_assoc': forall n m p:nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| n']. reflexivity.
  simpl. rewrite -> IHn'. reflexivity. Qed.
Theorem plus_0_r: forall n:nat, n + 0 = n.
Proof.
  intros n.
  induction n as [| n']. reflexivity.
  simpl. rewrite -> IHn'. reflexivity.  Qed.
 Check  minus.
Theorem minus_diag: forall n: nat, minus n n = 0.
Proof.
  intros n.
  induction n as [| n']. reflexivity.
  simpl. rewrite -> IHn'. reflexivity. Qed.
Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros n.
  induction n as [| n']. reflexivity.
  simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [| n']. simpl. reflexivity.
  simpl. rewrite -> IHn'. reflexivity. Qed.
Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
 intros n m.
  induction n as [| n']. simpl. rewrite -> plus_0_r. reflexivity.
  simpl. rewrite <- plus_n_Sm. rewrite -> IHn'. reflexivity. Qed.

Fixpoint double (n :nat) : nat :=
  match n with 
  | O => O
  | S n' => S (S (double n'))
  end.
Lemma double_plus : forall n, double n = n + n .
Proof.
  intros n.
  induction n as [| n']. reflexivity. 
  simpl.  rewrite <- plus_n_Sm. rewrite -> IHn'. reflexivity. Qed.

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
    rewrite -> plus_comm. reflexivity.
  rewrite -> H. reflexivity. Qed.

Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  assert (H: n + (m + p) = (n + m) + p). rewrite -> plus_assoc'. reflexivity.
  assert (H1: m + (n + p) = (m + n) + p). rewrite -> plus_assoc'. reflexivity.
  assert (H2: n + m = m + n). rewrite -> plus_comm.  reflexivity.
  rewrite -> H. rewrite -> H1. rewrite -> H2. reflexivity. Qed.

Theorem mult_n_sm: forall n m: nat,
  n*(S m) = n + n*m.
Proof.
  intros n m.
  induction n as [| n']. reflexivity.
  simpl. rewrite -> plus_swap. rewrite -> IHn'. reflexivity. Qed.

Theorem mult_comm : forall m n : nat,
 m * n = n * m.
Proof.
  intros m n.
  induction m as [| m']. rewrite -> mult_0_r. reflexivity.
  simpl. rewrite <- mult_n_Sm. rewrite -> plus_comm.
  rewrite -> IHm'. reflexivity. Qed.

Theorem eq_remove_S : forall n m : nat,
  n = m -> S n = S m.
Proof.
  intros n m H. rewrite -> H. reflexivity. Qed.

Theorem double_injective : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n. induction n as [| n']. 
  intros m H. induction m as [| m']. reflexivity. inversion H.
  intros m H. induction m as [| m']. inversion H.
  apply eq_remove_S. apply IHn'. inversion H. reflexivity. Qed.

Theorem eq_S : forall n m : nat,
  S n = S m -> n = m.
 Proof.
  intro n. induction n as [| n'].
  intros m H. inversion H. reflexivity.
  intros m H. inversion H. reflexivity. Qed. 

Theorem eq_Sn_plus_Sn_lemma : forall n : nat,
  S n + S n = S (S (n + n)).
Proof.
  intro n. induction n as [| n']. reflexivity.
  assert (H0: S (S n') + S (S n') = S (S (S n') + S n')). rewrite -> plus_n_Sm. reflexivity.
  rewrite -> H0. simpl. reflexivity. Qed.

Theorem eq_Sn_plus_Sn_to : forall n m : nat,
  S n + S n = S m + S m -> n + n = m + m.
 Proof.
  intros n m H.
  rewrite eq_Sn_plus_Sn_lemma in H.
  rewrite eq_Sn_plus_Sn_lemma in H.
  inversion H. reflexivity. Qed.

Theorem eq_Sn_plus_Sm_to : forall n m : nat,
  S n + S m = S (S (n + m)).
Proof.
  intros n. induction n as [| n'].
  intro m. reflexivity.
  intro m.
  assert (H0: S (S n') + S m = S (S (S n') + m)). rewrite -> plus_n_Sm. reflexivity.
  rewrite -> H0. reflexivity. Qed.
  
Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros n. induction n as [| n']. intros m H.
  induction m as [| m']. reflexivity. inversion H.
  intros m H. induction m as [| m']. inversion H.
  apply eq_remove_S. apply IHn'. apply eq_Sn_plus_Sn_to.
  assumption. Qed.
  

End nat3.