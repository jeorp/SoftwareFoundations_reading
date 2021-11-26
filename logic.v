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

 Theorem from_double_neg : forall P : Prop,
  ~~P -> P.
  intros P.  unfold not. intro H.
  Admitted.

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

Theorem eq_S : forall n m : nat,
  S n = S m -> n = m.
 Proof.
  intro n. induction n as [| n'].
  intros m H. inversion H. reflexivity.
  intros m H. inversion H. reflexivity. Qed. 

Theorem noteq_n_m_then_noteq_Sn_Sm : forall n m : nat,
  n <> m -> S n <> S m.
Proof.
  intros n m H.
  unfold not in H. unfold not. intro H0.
  apply H. apply eq_S. apply H0. Qed. 

Theorem noteq_Sn_Sm__noteq_n_m : forall n m : nat,
  (S n <> S m) <-> (n <> m).
Proof.
  intros n m. split.
  apply noteq_Sn_Sm_then_noteq_n_m.
  apply noteq_n_m_then_noteq_Sn_Sm. Qed.

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

Theorem zero_is_not_Sn : forall n : nat, 0 <> S n.
Proof.
  intro n. unfold not. intro H0. inversion H0. Qed.

Theorem noteq_sym : forall X : Type, forall p q : X,
  p <> q -> q <> p.
Proof.
  intros X P Q H. unfold not in H. unfold not. intro H0.
  apply H. rewrite -> H0. reflexivity. Qed.

Theorem beq_false_then__not_eq : forall n m,
  beq_nat n m = false -> n <> m.
Proof.
  intros n. induction n as [| n'].
  intros m H. induction m as [| m'].
  simpl in H. discriminate. apply zero_is_not_Sn.
  intros m H. induction m as [| m']. apply noteq_sym. apply zero_is_not_Sn.
  simpl in H. apply noteq_n_m_then_noteq_Sn_Sm. apply IHn'. apply H.
  Qed.

Theorem not_eq__beq_false : forall n n' : nat,
  (n <> n') <-> (beq_nat n n' = false).
Proof.
  intros n n'. split.
  apply not_eq_then_beq_false.
  apply beq_false_then__not_eq. Qed. 

Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS : forall n : nat, ev n -> ev (S (S n)).

Theorem four_ev' : ev 4.
Proof.
  apply ev_SS. apply ev_SS. apply ev_0. Qed.

Theorem ev_plus4' : forall n : nat,
  ev n -> ev (4 + n).
Proof.
  intros n H. simpl. apply ev_SS. apply ev_SS. assumption.
  Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Theorem double_even : forall n : nat,
  ev (double n).
Proof.
  intro n. induction n as [| n'].
  simpl. apply ev_0.
  simpl. apply ev_SS. apply IHn'. Qed.

Theorem SSev_even : forall n : nat,
  ev (S (S n)) -> ev n.
Proof.
  intros n E. inversion E as [| n' E']. apply E'. Qed.

Theorem ev_1_plus_m : forall m : nat,
  ev 1 -> ev m -> ev (1+m).
Proof.
  intros m H1 H2. inversion H1. Qed. 

Inductive ex (X : Type) (P : X -> Prop) : Prop :=
  ex_intro : forall (witness:X), P witness -> ex X P.

Notation "'exists' x , p" := (ex _ (fun x => p))
  (at level 200, x ident, right associativity) : type_scope.
Notation "'exists' x : X , p" := (ex _ (fun x:X => p))
  (at level 200, x ident, right associativity) : type_scope.


Example exists_example_1 : exists n, n + (n * n) = 6.
Proof.
  apply ex_intro with (witness:=2).
  reflexivity. Qed.

Example exists_example_1' : exists n,
     n + (n * n) = 6.
Proof.
  exists 2.
  reflexivity. Qed.

Theorem exists_example_2 : forall n,
     (exists m, n = 4 + m) ->
     (exists o, n = 2 + o).
Proof.
  intros n H.
  inversion H as [m Hm].
  exists (2 + m).
  apply Hm. Qed.

Theorem dist_not_exists : forall (X : Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros X P H. unfold not. intro H1. inversion H1.
  apply H0. apply H. Qed.


Definition peirce := forall P Q: Prop,
  ((P -> Q) -> P) -> P.
Definition classic := forall P : Prop,
  ~~P -> P.
Definition excluded_middle := forall P : Prop,
  P \/ ~P.
Definition de_morgan_not_and_not := forall P Q : Prop,
  ~(~P/\~Q) -> P \/ Q.
Definition implies_to_or := forall P Q : Prop,
  (P -> Q) -> (~P \/ Q).

Theorem exmiddle_classic : 
  excluded_middle -> classic.
Proof.
  unfold excluded_middle. unfold classic.
  intro H. intro P. unfold not. intro H1.
  assert (H2 : (P \/ ~P) -> ((P -> False) -> False) -> P).
  intros Hpnp Hpf. destruct Hpnp as [Hp | Hnp].
  apply Hp. unfold not in Hnp. apply Hpf in Hnp. inversion Hnp.
  apply H2. apply H. apply H1. Qed.

Theorem implies_to_or_ex_middle :
  implies_to_or -> excluded_middle.
Proof.
  intro H. unfold excluded_middle. unfold implies_to_or in H.
  intro P. apply or_comm. apply H. intro HP. apply HP. Qed.

Theorem peirce_to_classic :
  classic -> peirce.
Proof.
  intro H.  unfold peirce. unfold classic in H. unfold not in H.
  intros P Q. intro  H0.  Admitted.

Theorem morgan_classic : 
   de_morgan_not_and_not -> classic.
Proof.
  intro H. unfold classic. unfold  de_morgan_not_and_not in H.
  intro P. intro H0. 
  assert (Hl : ~~P -> ~(~ P /\ ~ P)). intro H'. 
  unfold not. unfold not in H'. intro H''. destruct H'' as [Hp Hq].
  apply H' in Hp. apply Hp.
  apply Hl in H0. apply H in H0. destruct H0 as [Hp | Hq].
  apply Hp. apply Hq. Qed.  

Theorem morgan_implies : 
   de_morgan_not_and_not -> implies_to_or.
Proof.
  intro H. unfold implies_to_or. unfold de_morgan_not_and_not in H.
  intros P Q. intro H0. apply H. Admitted.

Theorem morgan_exmiddle : 
   de_morgan_not_and_not -> excluded_middle.
Proof. Admitted.

Theorem x_to_exist : forall X : Type, forall P : X -> Prop, forall x : X,
  P x -> exists x, P x.
Proof.
  intros X P x. intro H. exists x. apply H. Qed.


Theorem not_exists_dist :
  excluded_middle ->
  forall (X :Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  intros H0. intros X P. intro H1. 
  intro x. unfold not in H1. assert (H : ((P x -> False) -> False) -> P x).
  intro H. assert (Hl : ((P x -> False) -> False)  = ~ (~ P x) ). unfold not. reflexivity.
  rewrite Hl in H. apply exmiddle_classic in H0. unfold classic in H0.
  apply H0. apply H. apply H. intro H2. Admitted.
  
  

Theorem dist_exists_or : forall (X :Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
Admitted.


Inductive le (n:nat) : nat -> Prop :=
  | le_n : le n n
  | le_S : forall m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).

Theorem test_le1 :
  3 <= 3.
Proof.
  apply le_n. Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  apply le_S. apply le_S. apply le_S. apply le_n. Qed.

Theorem test_le3 :
  ~ (2 <= 1).
Proof.
  intros H. inversion H. inversion H1. Qed.





End logic.