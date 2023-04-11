(* This is a comment *)

Definition two := 2.

Check two.

Compute two * (two + two).


(*  Successor function
    forall n in Nat:
        succ(n) = n + 1
 *)
Definition succ (n: nat) : nat := n + 1.
Check succ.
Compute succ 1.

Definition succ_implicit n := n + 1.
Check succ_implicit.
Compute succ_implicit 2.


(* Sum types *)
Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

Check day.
Check monday.

Definition next_weekday (d: day) : day :=
  match d with
    | monday => tuesday
    | tuesday => wednesday
    | wednesday => thursday
    | thursday => friday
    | friday|saturday|sunday => monday
  end.

Check next_weekday.
Compute next_weekday(monday).

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) =
  tuesday.

Proof. simpl. reflexivity. Qed.

Module MyNat.

Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

Definition one := S O.
Definition two := S one.
Definition three := S two.
Definition four := S three.
Definition five := S four.

Check (S (S (S (S O)))).
Compute (S (S (S (S O)))).

End MyNat.

Definition minustwo (n: nat) : nat :=
  match n with
  | S (S m) => m
  | _ => 0
  end.


Compute minustwo 0.
Compute minustwo 1.
Compute minustwo 2.
Compute minustwo 3.
Compute minustwo 4.

Fixpoint evenb (n: nat) : bool :=
  match n with
  | 0 => true
  | S 0 => false
  | S (S m) => evenb m
  end.

Compute evenb 0.
Compute evenb 1.
Compute evenb 2.
Compute evenb 3.
Compute evenb 4.

Fixpoint plus (n: nat) (m: nat) : nat :=
  match n with
  | 0 => m
  | S n' => S (plus n' m)
  end.

Compute plus 1 2.
Compute plus 0 5.
Compute plus 1000 2.
Compute plus 6 0.


Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | 0 => match m with
         | 0 => true
         | S _ => false
         end
  | S n' => match m with
            | 0 => false
            | S m' => beq_nat n' m'
            end
  end.

Check beq_nat.

Compute beq_nat 0 0.
Compute beq_nat 2 0.
Compute beq_nat 0 2.
Compute beq_nat 2 2.


Definition isZero (n: nat) : bool :=
  beq_nat n 0.

Check isZero.


(* This is too slow to load

Require Import Coq.Arith.Arith.

Definition isZero' (n: nat) : bool :=
  n =? 0.

Check isZero'.
 *)

Inductive natprod: Type :=
  | pair:  nat -> nat -> natprod .

Check (pair  0 2).

Definition fst (p : natprod) : nat :=
  match p with
  | (pair  f _) => f
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | (pair  _ s) => s
  end.

Check fst.
Check snd.

Compute fst (pair 0 2).
Compute snd (pair 0 2).

Check (pair 0 2).

Compute fst (pair 0 2).
Compute snd (pair 0 2).

Definition swap_pair (p: natprod) : natprod :=
  match p with
  | (pair m n) => (pair n m)
  end.


Lemma swap_twice: forall (m n : nat),
  swap_pair ( swap_pair (pair m n)) = (pair m n).

Proof.
  intros.
  simpl.
  reflexivity.
Qed.


Inductive natlist : Type :=
  | nil  : natlist
  | cons : nat -> natlist -> natlist.

Check nil.
Check cons 42.
Check (cons 23 (cons 42 nil)).

Fixpoint length (l: natlist) : nat :=
  match l with
  | nil => 0
  | cons _ l' => 1 + (length l')
  end.

Check length.
Compute length nil.
Compute length (cons 23 (cons 42 nil)).


