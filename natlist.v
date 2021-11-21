Module natlist.
Require Import Arith.
Check nat.
Check bool.

Inductive natlist: Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).
Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.
Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).
Example test_app1: [1,2,3] ++ [4,5] = [1,2,3,4,5].
Proof. reflexivity. Qed.
Example test_app2: nil ++ [4,5] = [4,5].
Proof. reflexivity. Qed.
Example test_app3: [1,2,3] ++ nil = [1,2,3].
Proof. reflexivity. Qed.

Fixpoint length (l: natlist): nat :=
  match l with
  | nil => O
  | cons a l' => S (length l')
  end.
Example test_length1 : (length []) = 0.
Proof. reflexivity. Qed.
Example test_length2: (length [1, 2, 3]) = 3.
Proof. reflexivity. Qed.

Fixpoint rev (l: natlist) : natlist :=
  match l with
  | nil => nil
  | cons a l1' => (rev l1') ++ [a]
  end.
Example test_rev1: (rev [1, 2, 3]) = [3, 2, 1].
Proof. reflexivity. Qed.
Example test_rev2: (rev [1]) = [1].
Proof. reflexivity. Qed.

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros l1 l2.
  induction l1 as [| n l1'].
  reflexivity.
  simpl. rewrite -> IHl1'. reflexivity. Qed.

Theorem app_ass : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3). 
Proof.
  intros l1 l2 l3.
  induction l1 as [| n l1']. reflexivity.
  simpl. rewrite -> IHl1'. reflexivity. Qed.

Theorem one_length : forall n: nat,
  length [n] = 1.
Proof.
  intro n. simpl. reflexivity. Qed. 
Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intro l.
  induction l as [| n l']. reflexivity.
  simpl. rewrite -> app_length.
  SearchRewrite(_ + _ ).
  rewrite -> Nat.add_comm.
  rewrite -> one_length. simpl.
  rewrite -> IHl'. reflexivity. Qed.
 

Theorem app_nil_end : forall l : natlist,
  l ++ [] = l.
Proof.
  intro l.
  induction l as [| n l']. reflexivity.
  simpl. rewrite -> IHl'. reflexivity. Qed.

Theorem rev_one : forall n : nat,
  rev [n] = [n].
 Proof. reflexivity. Qed. 

Theorem rev_rev_one : forall n : nat,
  rev (rev [n]) = [n].
 Proof. reflexivity. Qed. 

Theorem distr_rev : forall l1 l2 : natlist,
  rev (l1 ++ l2) = (rev l2) ++ (rev l1).
Proof.
  intros l1 l2.
  induction l1 as [| a l1']. simpl. rewrite -> app_nil_end. reflexivity.
  simpl. rewrite -> IHl1'. rewrite -> app_ass. reflexivity. Qed.
  
Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intro l.
  induction l as [| n l']. reflexivity.
  simpl. rewrite <-  rev_one.
  rewrite -> distr_rev.
  rewrite -> rev_rev_one. simpl.
  rewrite -> IHl'. reflexivity. Qed.

Theorem app_ass4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros l1 l2 l3 l4.
  rewrite -> app_ass.
  rewrite -> app_ass. reflexivity. Qed.

End natlist.
