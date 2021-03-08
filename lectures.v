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
  | 0 | S 0 => 0
  | S (S m) => m
  end.


Compute minustwo 4.
