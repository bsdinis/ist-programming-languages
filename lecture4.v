
Module Polymorphic.

  (* Lists *)

Inductive list (T: Type) : Type :=
  | nil : list T
  | cons : T -> list T -> list T .

Arguments nil {T}.
Arguments cons {T} _ _ .

Fixpoint repeat {T} v count : list T :=
  match count with
  | 0 => nil
  | S c' => (cons v (repeat v c'))
  end.

Fixpoint len {T} (l : list T) : nat :=
  match l with
  | nil => 0
  | (cons _ l') => 1 + (len  l')
  end.

Fixpoint append {T} (l1 l2 : list T) : list T :=
  match l1 with
  | nil => l2
  | (cons v l1') => (cons v (append l1' l2))
  end.

Fixpoint reverse {T} (l : list T) : list T :=
  match l with
  | nil => nil
  | (cons v l') => (append (reverse l') (cons v nil))
  end.

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil .
Notation "[ x , .. , y ]" := (cons x .. ( cons y nil ) .. ).
Notation "[ v ; c ]" := (repeat v c).

Check list.
Check nil.
Check cons.
Check (cons 1 nil).

Check [1, 2, 3, 4].
Check [1, 4, 3, 4].
Check [].
Check 1::34::[].
Compute [0; 20].
Compute [4; 5].
Compute [8; 0].
Compute [true; 3].

Check len [1, 4, 3, 4].
Compute len [1, 4, 3, 4].
Compute len [true; 9].

Compute (append [5; 4] [65, 62] ).
Compute (reverse [1, 2, 3, 4]).

(* we may need to supply explicit type parameters to help type inference *)
Definition mynil : list nat := nil.

(* we  can still make this generic,
   but we still may need to supply explicit type
   parameters to help type inference *)
Definition mynil' (X : Type) : list X := nil.


(* remove implicit type definition *)
Check @nil.
Check @nil nat.


  (* Pairs *)

Inductive prod (X Y: Type) : Type :=
  | pair : X -> Y -> prod X Y.

Arguments pair {X} {Y} _ _ .

Notation "( x , y )" := (pair x y).
(* type_scope means that this notation is only valid when parsing types

   this is great because this does not clash with regular multiplication *)
Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y: Type} (p: X * Y) : X :=
  match p with
  | (x, y) => x
  end.

Definition snd {X Y: Type} (p: X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

Notation "x .0" := (fst x) (at level 60).
Notation "x .1" := (snd x) (at level 60).

Compute (3 ,  true).
Compute (3 ,  true).0.
Compute (3 ,  true).1.

Fixpoint combine {X Y: Type} (l1: list X) (l2: list Y) : list (X * Y) :=
  match l1, l2 with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

(* Options *)

Inductive option (X: Type) : Type :=
  | Some : X -> option X
  | None : option X.

Arguments Some {X} _.
Arguments None {X}.

End Polymorphic.


Module HOF.

Require Import Coq.Lists.List.
Import ListNotations.

Fixpoint filter {X: Type} (test: X->bool) (l:list X) : (list X) :=
  match l with
  | [] => []
  | h :: t => if test h then h :: (filter test t)
                        else filter test t
  end.


End HOF.
