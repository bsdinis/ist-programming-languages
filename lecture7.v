(* programming languages *)

Inductive arith: Set :=
  | const (n: nat)
  | plus (a b: arith)
  | times (a b: arith).


Fixpoint size (root: arith) :  nat :=
  match root with
  | (const n) => 1
  | (plus a b)|(times a b) => 1 +  (size a) + (size b)
  end.

Compute (size (const 1)).
Compute (size (plus (const 1) (times (const 2) (const 4)))).

Fixpoint max (n : nat) (m : nat) : nat :=
  match n, m with
    | O, O => O
    | O, S x => S x
    | S x, O => S x
    | S x, S y => S (max x y)
  end.

Fixpoint depth (root: arith): nat :=
  match root with
  | (const n) => 0
  | (plus a b)|(times a b) => 1 + (max (depth a) (depth b))
  end.

Compute (depth (const 1)).
Compute (depth (plus (const 1) (times (const 2) (const 4)))).
Compute (depth (plus (const 1) (times (plus (const 2) (const 3)) (const 4)))).
