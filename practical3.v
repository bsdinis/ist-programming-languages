Module BinTree.

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Arith.
Require Import Lia.

Inductive btree (T: Type) : Type  :=
  | empty
  | node: T -> btree T -> btree T -> btree T.

Arguments empty {T}.
Arguments node {T} _ _ _ .

Fixpoint nodes {T: Type} (t: btree T) : nat :=
  match t with
  | empty => 0
  | node _ l r => 1 + (nodes l) + (nodes r)
  end.

Compute (nodes (node 1 (node 2 empty (node 3 empty empty)) (node 4 empty empty))).

Compute (nodes (empty)).


Fixpoint leaves {T: Type} (t: btree T) : nat :=
  match t with
  | empty => 1
  | node _ a b => leaves a + leaves b
  end.

Compute (leaves (node 1 (node 2 empty (node 3 empty empty)) (node 4 empty empty))).
Compute (leaves (empty)).

Fixpoint append {T: Type} (l1 l2: list T) : list T :=
  match l1, l2 with
  | [], _ => l2
  | _, [] => l1
  | (h::t), l2 => h:: (append t l2)
  end.

Fixpoint flatten {T: Type} (t: btree T) : list T :=
  match t with
  | empty => []
  | node v a b => (append (v::(flatten a)) (flatten b))
  end.

Compute (flatten (node 1 (node 2 empty (node 3 empty empty)) (node 4 empty empty))).
Compute (flatten (empty)).


Fixpoint height {T: Type} (t: btree T) : nat :=
  match t with
  | empty => 0
  | node _ a b => 1 + (max (height a) (height b))
  end.

Compute (height (node 1 (node 2 empty (node 3 empty empty)) (node 4 empty empty))).
Compute (height (empty)).


(*
Lemma max_lt: forall a b:nat, (max a b) <= a + b.
Proof .
    intros a b.
    case (le_lt_dec a b).
    - rewrite <- Nat.max_r_iff; intros ->; lia.
    - intros H_b_lt_a; apply Nat.lt_le_incl, Nat.max_l_iff in H_b_lt_a; rewrite H_b_lt_a; lia.
Qed.


Lemma both_S: forall a b: nat, (S a <= S b) -> (a <= b).

Proof.
  intros a b.
  induction a as [| a' IHa].
  - lia.
  - intros. apply IHa in H.
Qed.
*)

Lemma height_number: forall (T: Type) (t: btree T), height t <= nodes t.
Proof.
  intros T tree.
  induction tree; simpl; lia.
Qed.


Fixpoint maxTree (t: btree nat): nat :=
  match t with
  | empty => 0
  | node v l r => (max (max v (maxTree l)) (maxTree r))
  end.


Compute (maxTree (node 1 (node 2 empty (node 3 empty empty)) (node 4 empty empty))).
Compute (maxTree (empty)).

Fixpoint subTrees {T: Type} (t: btree T) : list (btree T) :=
  match t with
  | empty => []
  | node _ l r => (append (t::(subTrees l)) (subTrees r))
  end.

Compute (subTrees (node 1 (node 2 empty (node 3 empty empty)) (node 4 empty empty))).
Compute (subTrees (empty)).

Fixpoint mapBTree {T U: Type} (t: btree T) (f: T -> U) : btree U :=
  match t with
  | empty => empty
  | node t l r => node (f t) (mapBTree l f) (mapBTree r f)
  end.

Compute (mapBTree (node 1 (node 2 empty (node 3 empty empty)) (node 4 empty empty)) (fun x => x <=? 2) ).

Fixpoint foldBTree {T U: Type} (f: T -> U -> U -> U) (l: btree T) (initial: U) : U :=
  match l with
  | empty => initial
  | node t l r => f t (foldBTree f l initial)  (foldBTree f r initial)
  end.

Fixpoint nodes' {T: Type} (t: btree T) : nat :=
  foldBTree (fun t l r => l + r + 1) t 0.

Compute (nodes (node 1 (node 2 empty (node 3 empty empty)) (node 4 empty empty))).
Compute (nodes (empty)).
Compute (nodes' (node 1 (node 2 empty (node 3 empty empty)) (node 4 empty empty))).
Compute (nodes' (empty)).

Fixpoint leaves' {T: Type} (t: btree T) : nat :=
  foldBTree (fun t l r => l + r) t 1.

Compute (leaves (node 1 (node 2 empty (node 3 empty empty)) (node 4 empty empty))).
Compute (leaves (empty)).
Compute (leaves' (node 1 (node 2 empty (node 3 empty empty)) (node 4 empty empty))).
Compute (leaves' (empty)).

Fixpoint flatten' {T: Type} (t: btree T) : list T :=
  foldBTree (fun t l r => append (t::l) r) t [].

Compute (flatten (node 1 (node 2 empty (node 3 empty empty)) (node 4 empty empty))).
Compute (flatten (empty)).
Compute (flatten' (node 1 (node 2 empty (node 3 empty empty)) (node 4 empty empty))).
Compute (flatten' (empty)).

Fixpoint height' {T: Type} (t: btree T) : nat :=
  foldBTree (fun t l r => 1 + (max l  r)) t 0.

Compute (height (node 1 (node 2 empty (node 3 empty empty)) (node 4 empty empty))).
Compute (height (empty)).
Compute (height' (node 1 (node 2 empty (node 3 empty empty)) (node 4 empty empty))).
Compute (height' (empty)).

Fixpoint maxTree' (t: btree nat): nat :=
  foldBTree (fun t l r => max t (max l  r)) t 0.

Compute (maxTree (node 1 (node 2 empty (node 3 empty empty)) (node 4 empty empty))).
Compute (maxTree (empty)).
Compute (maxTree' (node 1 (node 2 empty (node 3 empty empty)) (node 4 empty empty))).
Compute (maxTree' (empty)).

Fixpoint mapBTree' {T U: Type} (t: btree T) (f: T -> U) : btree U :=
  foldBTree (fun t l r => node (f t) l  r) t empty.

Compute (mapBTree (node 1 (node 2 empty (node 3 empty empty)) (node 4 empty empty)) (fun x => x <=? 2) ).
Compute (mapBTree' (node 1 (node 2 empty (node 3 empty empty)) (node 4 empty empty)) (fun x => x <=? 2) ).

End BinTree.
