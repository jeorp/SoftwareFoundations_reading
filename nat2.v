Module nat2.

Check nat.
Fixpoint plus (a: nat) (b: nat) : nat :=
  match a with
  | O => b
  | S a' => S (plus a' b)
  end.
Fixpoint mult (a: nat) (b: nat): nat :=
  match a with 
  | O => O
  | S a' => plus b (mult a' b)
  end.
Fixpoint minus (a: nat) (b: nat) :=
  match a, b with
  | O,  _ => O
  | _ , O => O
  | S a', S b' => minus a' b'
  end.
Fixpoint factorial (n: nat) : nat :=
  match n with
  | O => S O
  | S n' => mult n (factorial n')
  end.
 Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2: (factorial 5) = 120.
Proof. simpl. reflexivity. Qed.
End nat2.
 
