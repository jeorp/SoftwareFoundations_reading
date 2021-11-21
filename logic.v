Module logic.

Definition tautology : Prop :=
  forall P : Prop, P -> P.
Theorem proof_tautology : tautology.
Proof.
 intros P H. assumption. Qed.

Theorem prop_trans : forall P Q R : Prop,
  (P -> Q) -> (Q -> R) -> (P -> R).
Proof.
  intros P Q R H0 H1.
  intros H.
  apply H1. apply H0. apply H. Qed.

Inductive and (P Q : Prop) : Prop :=
  conj : P -> Q -> (and P Q).
Check  and.
Notation "P /\ Q" := (and P Q) : type_scope.
Check conj.

Theorem proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q H.
  inversion H as [HP HQ].
  apply HP. Qed.  

Theorem proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros P Q H.
  inversion H as [HP HQ].
  assumption. Qed.

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q H.
  inversion H as [HP HQ].
  split.
  apply HQ.
  apply HP. Qed.
Print and_commut.

Theorem and_assoc : forall P Q R : Prop,
  (P /\ Q) /\ R -> P /\ (Q /\ R).
Proof.
  intros P Q R H.
  inversion H as [[HP HQ] HR].
  split. apply HP.
 split. apply HQ. apply HR. Qed.

Theorem conj_fact : forall P Q R : Prop,
  P /\ Q -> Q /\ R -> P /\ R.
Proof.
  intros P Q R H0 H1.
  inversion H0 as [HP HQ].
  inversion H1 as [_ HR].
 split. apply HP. apply HR. Qed.

Definition iff (P Q : Prop) : Prop := (P -> Q) /\ (Q -> P).
Notation "P <-> Q" := (iff P Q) (at level 95, no associativity) : type_scope.
Check 1=1 <-> 2=2.

Theorem iff_implies : forall P Q :Prop,
  P <-> Q -> P -> Q.
 Proof.
  intros P Q H. inversion H as [HPQ HQp]. apply HPQ. Qed.

Theorem iff_sym : forall P Q : Prop, 
  P <-> Q -> Q <-> P.
Proof.
  intros P Q H.
  inversion H as [HPQ HQP].
  split. apply HQP. apply HPQ. Qed.

Theorem iff_refl : forall P : Prop, P <-> P.
  intro P.
 split. apply proof_tautology. apply proof_tautology. Qed.

Theorem iff_trans : forall P Q R : Prop,
  P <-> Q -> Q <-> R -> P <-> R.
Proof.
  intros P Q R H0 H1.
  inversion H0 as [HPQ HQP].
  inversion H1 as [HQR HRQ].
  assert (HPR : P -> R). intro H'. apply HQR. apply HPQ. apply H'.
  assert (HRP: R -> P). intro H'. apply HQP. apply HRQ. apply H'.
 split. apply HPR. apply HRP. Qed.

Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q.
Check or_introl.
Notation "P \/ Q" := (or P Q) : type_scope.
Theorem or_comm : forall P Q : Prop,
  (P \/ Q) -> (Q \/ P).
Proof.
  intros P Q H.
  inversion H as [HP | HQ].
  apply or_intror. apply HP.
  apply or_introl. apply HQ. Qed.

Theorem or_distributes_over_and_1 : forall P Q R : Prop,
  P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R H.
  inversion  H as [HP | HQandR].
  split.
  apply or_introl. apply HP.
  apply or_introl. apply HP.
  inversion HQandR as [HQ HR].
  split.
  apply or_intror. apply HQ.
  apply or_intror. apply HR. Qed.

Theorem or_distributes_over_and_2 : forall P Q R : Prop,
  (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
Proof.
  intros P Q R H.
  inversion H as [HPandQ HPandR].
  inversion HPandQ as [HP | HQ].
  inversion HPandR as [_ | HR].
  apply or_introl.  apply HP.
  apply or_introl.  apply HP.
  inversion HPandR as [HP | HR].
  apply or_introl. apply HP.
  apply or_intror. split. apply HQ. apply HR. Qed.

Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R.
  split.
  apply or_distributes_over_and_1.
 apply  or_distributes_over_and_2. Qed. 

Theorem andb_true__and : forall b c : bool,
  andb b c = true -> b = true /\ c = true.
Proof.
  intros b c H.
  destruct b. split. reflexivity.
  destruct c. reflexivity. discriminate.
  split. discriminate.
  destruct c. reflexivity. discriminate. Qed.

Theorem and__andb_true : forall b c : bool,
  b = true /\ c = true -> andb b c = true.
Proof.
  intros b c H. inversion H as [Hb Hc].
  rewrite -> Hb. rewrite -> Hc. reflexivity. Qed.

Theorem andb_true_theorem : forall b c : bool,
  (andb b c = true) <-> (b = true /\ c = true).
Proof.
  intros b c. split.
  apply andb_true__and. apply and__andb_true. Qed.

Theorem andb_false__or : forall b c : bool,
  andb b c = false -> b = false \/ c = false.
Proof.
  intros b c H.
  destruct b. apply or_intror. destruct c. simpl in H. apply H.
  reflexivity.
  apply or_introl. reflexivity. Qed. 

Theorem andb_comm : forall b c : bool,
  andb b c = andb c b.
Proof.
  intros b c.
  destruct b.
  destruct c. reflexivity. reflexivity.
  destruct c. reflexivity. reflexivity. Qed.

Theorem or__andb_false : forall b c : bool,
  b = false \/ c = false -> andb b c = false.
Proof.
  intros b c H.
  inversion H as [Hb | Hc].
  rewrite -> Hb. reflexivity.
  rewrite -> Hc. rewrite -> andb_comm. reflexivity. Qed. 

Theorem andb_false_theorem : forall b c : bool,
  (andb b c = false) <-> (b = false \/ c = false).
Proof.
  intros b c.
  split.
  apply andb_false__or.
  apply or__andb_false. Qed.

Theorem orb_true__or : forall b c : bool,
  orb b c = true -> b = true \/ c = true.
Proof.
  intros b c H.
  destruct b. apply or_introl. reflexivity.
  destruct c. apply or_intror. reflexivity.
  simpl in H. discriminate. Qed. 

Theorem orb_comm : forall b c :bool,
  orb b c = orb c b.
Proof.
  intros b c.
  destruct b.
  destruct c. reflexivity. reflexivity.
  destruct c. reflexivity. reflexivity. Qed.
  
Theorem or__orb_true : forall b c : bool,
  b = true \/ c = true -> orb b c = true.
Proof.
  intros b c H.
  inversion H as [Hb | Hc].
  rewrite -> Hb. reflexivity.
  rewrite -> Hc. rewrite -> orb_comm. reflexivity. Qed.

Theorem orb_true_theorem : forall b c : bool,
  (orb b c = true) <-> (b = true \/ c = true).
Proof.
  intros b c. split.
  apply orb_true__or.
  apply or__orb_true. Qed.

Theorem orb_false__and : forall b c : bool,
  orb b c = false -> b = false /\ c = false.
Proof.
  intros b c H.
  destruct b. 
  destruct c.
  simpl in H. discriminate.
  simpl in H. discriminate.
  destruct c.
  simpl in H. discriminate.
  split. reflexivity. reflexivity. Qed.
  
Theorem and__orb_false : forall b c : bool,
  b = false /\ c = false -> orb b c = false.
Proof.
  intros b c H.
  inversion H as [Hb Hc].
  rewrite -> Hb. rewrite Hc. reflexivity. Qed.

Theorem orb_false_theorem : forall b c : bool,
  (orb b c = false) <-> (b = false /\ c = false).
Proof.
  intros b c. split.
  apply orb_false__and.
  apply and__orb_false. Qed.

Inductive False : Prop := .
Theorem False_implies_nonsence : 
  False -> true = false.
Proof.
  intro H. inversion H. Qed.
Theorem nonsence_implies_False :
  true = false -> False.
 Proof.
  intro H. inversion H. Qed.
Theorem eq_False_nonsence : 
  true = false <-> False.
 Proof.
  split.
  apply nonsence_implies_False.
  apply False_implies_nonsence. Qed.
Theorem ex_falso_quodlibet : forall P : Prop,
  False -> P.
Proof.
  intros P H. inversion H. Qed.

Inductive True : Prop := tl : False -> True.
Definition not (P : Prop) : Prop :=  P -> False.
Notation "~ x" := (not x) : type_scope.
Check not.

Theorem not_False :  ~ False.
Proof.
  intro F. inversion F. Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  intros P Q H.
  inversion H as [HP HnotP].
  apply HnotP in HP. inversion HP. Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof. 
  intros P H0. intro H. apply H. apply H0. Qed. 

Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q H. intro HQ. intro HP.
  apply HQ. apply H. apply HP. Qed.
  
Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  intro P. intro H.
  inversion H as [HP HnotP].
  apply HnotP. apply HP. Qed.

Notation "x <> y" := (~ (x = y)) : type_scope.

Theorem not_false_then_true : forall b,
  b <> false -> b = true.
Proof.
  intros b H. destruct b.
  reflexivity.
  unfold not in H. apply ex_falso_quodlibet.
  apply H. reflexivity. Qed.

Theorem true_then_not_false : forall b : bool,
  b = true -> b <> false.
Proof.
  intros b H. unfold not.
  destruct b. intro H0. 
  discriminate. discriminate. Qed. 
 
Theorem true_is_not_false : forall b : bool,
  (b <> false) <-> (b = true).
Proof.
  intros b. split.
  apply not_false_then_true.
  apply true_then_not_false. Qed.

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

Theorem noteq_Sn_Sm_then_noteq_n_m : forall n m : nat,
  S n <> S m -> n <> m.
Proof.
  intros n m H. unfold not in H. unfold not.
  intro H0. apply H. rewrite -> H0. reflexivity. Qed.

Theorem noteq_n_m_then_noteq_Sn_Sm : forall n m : nat,
  n <> m -> S n <> S m.
Proof.
Admitted.

Theorem noteq_Sn_Sm__noteq_n_m : forall n m : nat,
  (S n <> S m) <-> (n <> m).
Proof.
Admitted.

Theorem not_eq_then_beq_false : forall n1 n2 : nat,
  n1 <> n2 -> beq_nat n1 n2 = false.
Proof.
  intros n1.  induction n1 as [| n1'].
  intros n2 H. induction n2 as [| n2'].
  simpl. unfold not in H. apply False_implies_nonsence. apply H. reflexivity.
  simpl. reflexivity. 
  intros n2 H. induction n2 as [| n2'].
  simpl. reflexivity.
  simpl. rewrite IHn1'. reflexivity. apply noteq_Sn_Sm_then_noteq_n_m.
  apply H. Qed.

Theorem beq_false_then__not_eq : forall n m,
  false = beq_nat n m -> n <> m.
Proof.
Admitted.

Theorem not_eq__beq_false : forall n n' : nat,
  (n <> n') <-> (beq_nat n n' = false).
Proof.
Admitted.

End logic.