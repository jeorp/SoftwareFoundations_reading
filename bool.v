Module Localbool.
Inductive bool : Type :=
  | true : bool
  | false : bool.

Definition negb (b: bool) : bool :=
  match b with 
    | true => false
    | false => true
  end.
Definition andb (a: bool) (b: bool) : bool :=
  match a with
    | true => b
    | false => false
  end.
Example test_negb:  (negb false) = true.
Proof. simpl. reflexivity. Qed.
Example test_and1: (andb true false) = false.
Proof. simpl. reflexivity. Qed.
Example test_and2: (andb false true) = false. 
Proof. simpl. reflexivity. Qed.
Example test_and3: (andb true true) = true.
Proof. simpl. reflexivity. Qed.

End Localbool.



