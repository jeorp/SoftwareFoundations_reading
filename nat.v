Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

Definition pred (n : nat) : nat := 
  match n with
    | O => O
    | S n' => n'
  end.

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.
Check S.
Check pred.
Check minustwo.

Fixpoint evenb (n: nat) : bool :=
  match n with
    | O => true
    | S O => false
    | S (S n') => evenb n'
  end.
Definition oddb (n: nat) : bool := negb (evenb n).

Example test_even1: (evenb (S (S (S O)))) = false.
Proof. simpl. reflexivity. Qed.
Example test_odd1: (oddb (S (S (S O)))) = true.
Proof. simpl. reflexivity. Qed.
Example test_odd2: (oddb ((S (S O)))) = false.
Proof. simpl. reflexivity. Qed.




