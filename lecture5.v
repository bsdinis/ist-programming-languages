Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.PeanoNat.

Fixpoint filter {T: Type} (test: T -> bool) (l: list T) : (list T) :=
  match l with
  | [] => []
  | h :: t => if test h then h :: (filter test t)
                        else filter test t
  end.

Fixpoint oddnat (n: nat) : bool :=
  match n with
  | 0 => false
  | 1 => true
  | S (S n') => oddnat n'
  end.

Definition countoddmembers (l: list nat) :=
  length (filter oddnat l).

Compute countoddmembers [1;2;3;4;5;6;7].
Compute countoddmembers [1;2;3;4;5;6;7;7].

Definition remove_smaller_than (n: nat) (l: list nat) : (list nat) :=
  filter (fun x => n <=? x) l.

Compute remove_smaller_than 3 [1;2;3;4;5].
Compute remove_smaller_than 3 [7;1;2;3;4;5].

Fixpoint map {T U: Type} (f: T -> U) (l: list T) : (list U) :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.

Compute map (fun x => x + 3) [1;3;5;7].

(* this is simply a reduce operation
   fold (fun x y => x + y) [1;2;3;4;5] 0.
   sums the list
 *)

Fixpoint fold {T U: Type} (f: T -> U -> U) (l: list T) (initial: U) : U :=
  match l with
  | [] => initial
  | h :: t => f h (fold f t initial)
  end.


(* this function returns a function which, no matter with
  integer it is passed, returns a constant x *)
Definition constfun {T:Type} (t: T) : nat -> T :=
  fun (k:nat) => t.

Compute constfun(true).
Compute (constfun(true) 7).
Compute (constfun(true) 0).

Definition length' {T: Type} (l: list T) : nat :=
  fold (fun _ y => y + 1) l 0.

Compute length' [1;2;3;4;5].
Compute length' [1].
Compute length' [].

Definition map' {T U: Type} (f: T -> U) (l: list T): (list U) :=
  fold (fun head accumulator => ( f head ) :: accumulator) l [].

Compute map (fun x => x + 3) [1;3;5;7].
Compute map' (fun x => x + 3) [1;3;5;7].

(* proofs *)

Theorem plus_0_n: forall n : nat, 0 + n = n.

Proof.
  intros n. (* without loss of generality: remove forall *)
  simpl. (* simplify the expression: this will apply the plus definition and remove the simplification *)
  reflexivity. (* X = X is true *)
Qed.


Theorem plus_1_l: forall n : nat, 1 + n = S n.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.

Theorem mult_0_l : forall n, 0 * n = 0.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.


Theorem plus_identity_example: forall n  m : nat, n = m -> n + n = m + m.
Proof.
  intros n m.
  intros H. (* H == Hypothesis *)
  rewrite -> H. (* apply the hypothesis *)
  reflexivity.
Qed.


Theorem plus_identity_exercise: forall n m o: nat, n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H.
  intros L.
  rewrite -> H.
  rewrite -> L.
  reflexivity.
Qed.


Theorem mult_S_1: forall n m: nat,
  m = 1 + n ->
  m * ( 1 + n ) = m * m.
Proof.
  intros n m.
  intros H.
  rewrite -> H.
  reflexivity.
Qed.

Theorem mult_0_plus: forall n m: nat,
  ( 0 + n ) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_0_n.
  reflexivity.
Qed.



