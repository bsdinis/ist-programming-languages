(* programming languages *)

Load Maps.
Load TacticsLP.

Require Import Coq.Arith.PeanoNat.
Require Import Arith.
Require Import Lia.

Notation var := string.
Definition valuation := partial_map nat.

Inductive let_ast: Type :=
  | Let (var : string) (val: let_ast) (next: let_ast)
  | Const (n: nat)
  | Var (x : string)
  | Plus (a b: let_ast)
  | Times (a b: let_ast).


Fixpoint size (root: let_ast) :  nat :=
  match root with
  | Const _ | Var _ => 1
  | Let _ a b |Plus a b|Times a b => 1 + (size a) + (size b)
  end.

Compute (size (Const 1)).
Compute (size (Plus (Const 1) (Times (Const 2) (Const 4)))).


Fixpoint depth (root: let_ast): nat :=
  match root with
  | Const _ | Var _ => 1
  | Let _ a b |Plus a b|Times a b => 1 + (max (depth a) (depth b))
  end.

Compute (depth (Const 1)).
Compute (depth (Plus (Const 1) (Times (Const 2) (Const 4)))).
Compute (depth (Plus (Const 1) (Times (Plus (Const 2) (Const 3)) (Const 4)))).

Theorem depth_le_size: forall e,
  depth e <= size e.

Proof.
  intros e.
  induction e; simpl; lia.
Qed.

Fixpoint commuter (root: let_ast): let_ast :=
  match root with
  | Let x v n => Let x (commuter v) (commuter n)
  | Plus a b => Plus (commuter b) (commuter a)
  | Times a b => Times (commuter b) (commuter a)
  | _ => root
  end.

Compute (commuter (Const 1)).
Compute (commuter (Plus (Const 1) (Times (Const 2) (Const 4)))).
Compute (commuter (Plus (Const 1) (Times (Plus (Const 2) (Const 3)) (Const 4)))).

Theorem size_commuter: forall e, size (commuter e) = size e.
Proof.
  induction e; simpl; lia.
Qed.

Theorem depth_commuter: forall e, depth (commuter e) = depth e.
Proof.
  induction e; simpl; lia.
Qed.

Theorem commuter_inverse: forall e, commuter (commuter e) = e.
Proof.
  induction e; simpl; equality.
Qed.


Fixpoint substitute (orig: let_ast) (variable: var) (new_node: let_ast) : let_ast :=
  match orig with
  | Const _ => orig
  | Let x v n => Let x (substitute v variable new_node) (substitute n variable new_node)
  | Var x => if x =? variable then new_node else orig
  | Plus e1 e2 => Plus (substitute e1 variable new_node) (substitute e2 variable new_node)
  | Times e1 e2 => Times (substitute e1 variable new_node) (substitute e2 variable new_node)
  end.

Theorem substitute_depth : forall orig variable new_node,
      depth (substitute orig variable new_node)
      <= depth orig + depth new_node.
Proof.
  intros.
  induction orig as [| | x | | ]; simpl; try lia.
  destruct (x =? variable) eqn: Heq; simpl; try lia.
Qed.


Theorem substitute_self : forall orig variable,
  substitute orig variable (Var variable) = orig.
Proof.
  intros. induction orig as [| | x | | ]; simpl; try equality.
  destruct (x =? variable) eqn: Heq; try equality.
  - rewrite eqb_eq in Heq; rewrite Heq; reflexivity.
Qed.


Theorem substitute_commuter : forall orig variable new_node,
  commuter (substitute orig variable new_node)
= substitute (commuter orig) variable (commuter new_node).
Proof.
  intros. induction orig as [| | x | | ]; simpl; try equality.
  destruct (x =? variable) eqn: Heq; try equality.
Qed.


Fixpoint eval (e: let_ast) (v: valuation) : nat :=
  match e with
  | Let var val next => eval next ( var |-> (eval val v); v)
  | Const n => n
  | Var x => match v x with
             | None => 0
             | Some n => n
             end
  | Plus e1 e2 => eval e1 v + eval e2 v
  | Times e1 e2 => eval e1 v * eval e2 v
  end.

Definition let_prog1 := (Let "x" (Const 1) (Let "y" (Const 2) (Plus (Var "x") (Var "y"))) ).
Compute eval let_prog1 (empty).

Definition let_prog2 := (Let "x" (Const 1) (Let "y" (Const 2) (Plus (Var "x") (Times (Var "y") (Var "z"))))).
Compute eval let_prog2 (empty).
Compute eval let_prog2 ("z" |-> 10).
