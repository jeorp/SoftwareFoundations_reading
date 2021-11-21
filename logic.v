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
Proof. Admitted.

Theorem and__andb_true : forall b c : bool,
  b = true /\ c = true -> andb b c = true.
Proof. Admitted.

Theorem andb_true_theorem : forall b c : bool,
  (andb b c = true) <-> (b = true /\ c = true).
Proof. Admitted.

Theorem andb_false__or : forall b c : bool,
  andb b c = false -> b = false \/ c = false.
Proof.
Admitted.

Theorem or__andb_false : forall b c : bool,
  b = false \/ c = false -> andb b c = false.
Proof.
Admitted.

Theorem andb_false_theorem : forall b c : bool,
  (andb b c = false) <-> (b = false \/ c = false).
Proof.
Admitted.

Theorem orb_true__or : forall b c : bool,
  orb b c = true -> b = true \/ c = true.
Proof.
Admitted.

Theorem or__orb_true : forall b c : bool,
  b = true \/ c = true -> orb b c = true.
Proof.
Admitted.

Theorem orb_true_theorem : forall b c : bool,
  (orb b c = true) <-> (b = true \/ c = true).
Proof.
Admitted.

Theorem orb_false__and : forall b c : bool,
  orb b c = false -> b = false /\ c = false.
Proof.
Admitted.

Theorem and__orb_false : forall b c : bool,
  b = false /\ c = false -> orb b c = false.
Proof.
Admitted.

Theorem orb_false_theorem : forall b c : bool,
  (orb b c = false) <-> (b = false /\ c = false).
Proof.
Admitted.


End logic.