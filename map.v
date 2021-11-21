Module map.
Require Import Arith.
Inductive list (X : Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.
 Check nil.
Check (cons nat 2 (nil nat)).

Fixpoint length (X:Type) (l:list X) : nat :=
  match l with
  | nil _ => 0
  | cons _ h t => S (length _ t)
  end.

Fixpoint length' {X: Type} (l: list X) : nat :=
  match l with
  | nil _ => 0
  | cons _ h t => S (length' t)
  end.

Arguments nil {_}.
Arguments cons {_} h t.
Check nil.
Check cons.

Fixpoint length'' {X: Type} (l: list X) : nat :=
  match l with
  | nil  => 0
  | cons  h t => S (length' t)
  end.
Example test_length'': length'' (cons 1 nil) = 1.
Proof. simpl. reflexivity. Qed.

Fixpoint app {X: Type} (l1 l2 : list X) : list X :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.
Example test_app1:
  app (cons 1 (cons 2 nil)) (cons 3 nil) = (cons 1 (cons 2 (cons 3 nil))).
 Proof. simpl. reflexivity. Qed.

Fixpoint rev {X: Type} (l: list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.
Example test_rev1:
  rev (cons 1 (cons 2 (cons 3 nil))) =  (cons 3 (cons 2 (cons 1 nil))). 
 Proof. simpl. reflexivity. Qed.
Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).
Example test_app2 : (cons 1 (cons 2 (cons 3 nil))) = [1, 2, 3].
 Proof. simpl. reflexivity. Qed.


Fixpoint repeat {X : Type} (n : X) (count : nat) : list X :=
  match count with
  | O => []
  | S c' => n :: (repeat n c')
  end.
Example test_repeat1:
  repeat true 2 = [true, true].
Proof. reflexivity. Qed.

Theorem nil_app : forall X : Type, forall l : list X,
  app [] l = l.
Proof.
  intros X l. reflexivity. Qed.

Inductive prod (X Y: Type) : Type :=
  pair : X -> Y -> prod X Y.
Check pair.
Check pair _ _ 1 2.
Arguments pair {_} {_} x y.
Check pair.
Check pair 1 [1].
Notation "( x , y )" := (pair x y).
Check (1, 3).
Notation "X * Y" := (prod X Y) : type_scope.
Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with (x,y) => x end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with (x,y) => y end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match (lx,ly) with
  | ([],_) => []
  | (_,[]) => []
  | (x::tx, y::ty) => (x,y) :: (combine tx ty)
  end.

Inductive option (X: Type) : Type :=
  | Some : X -> option X
  | None: option X.
Arguments Some {_} x.
Arguments None {_}.
Check Some 2.
Check None.

Definition head {X: Type} (l : list X) : option X :=
  match l with
  | nil => None
  | h::t => Some h
  end.
Example test_head1 : head [2, 4] = Some 2.
Proof. reflexivity. Qed.

Fixpoint filter {X:Type} (test: X -> bool) (l:list X)
                : (list X) :=
  match l with
  | [] => []
  | h :: t => if test h then h :: (filter test t)
                        else filter test t
  end.

Fixpoint map {X Y: Type} (f : X -> Y) (l : list X) : list Y :=
  match l with
  | nil => nil
  | x :: t => f x :: (map f t)
  end.
Example test_map1 : map (plus 2) [1, 2, 3] = [3, 4, 5].
Proof. reflexivity. Qed. 

Theorem map_assoc : forall (X Y: Type) (f: X -> Y) (l1 l2: list X),
   map f (l1 ++ l2) = (map f l1) ++ (map f l2).
Proof.
  intros X Y f l1 l2.
  induction l1 as [| n l1']. reflexivity.
  simpl. rewrite -> IHl1'. reflexivity. Qed. 
  

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros X Y f l.
  induction l as [| n l']. reflexivity.
  simpl. rewrite -> map_assoc. simpl. rewrite -> IHl'. reflexivity. Qed.

Fixpoint foldr {X Y : Type} (f : X -> Y -> Y) (l : list X) (b : Y) : Y :=
  match l with 
  | nil => b
  | h :: t => f h (foldr f t b)
  end.
Example test_foldr1 : foldr plus [1, 2, 3, 4] 0 = 10.
Proof. reflexivity. Qed.


End map.