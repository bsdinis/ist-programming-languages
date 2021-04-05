(* programming languages *)

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Arith.
Require Import Lia.

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

Lemma s_eq: forall (a b: nat),
  a <= b <-> S a <= S b.

Proof.
  intros.
  lia.
Qed.

Lemma max_0: forall a: nat,
  (max 0 a) = a.

Proof.
  intros.
  induction a; simpl; lia.
Qed.

Lemma max_leq: forall a b:nat,
  (max a b) <= a + b.

Proof.
  intros.
  destruct a as [|a'].
  - rewrite -> max_0. lia.
Admitted.


Theorem depth_le_size: forall e,
  depth e <= size e.

Proof.
  intros e.
  induction e as [| e1 IHe1 | e2 IHe2]; simpl; try lia; rewrite <- s_eq.
  - rewrite max_leq. lia.
    simpl.
    rewrite IHe1.
