(* programming languages *)

Load Maps.
Load TacticsLP.

Require Import Coq.Arith.PeanoNat.
Require Import Arith.
Require Import Lia.

Notation var := string.
Definition valuation := partial_map nat.

Inductive arith: Type :=
  | Const (n: nat)
  | Var (x : string)
  | Plus (a b: arith)
  | Times (a b: arith).


Fixpoint size (root: arith) :  nat :=
  match root with
  | Const _ | Var _ => 1
  | (Plus a b)|(Times a b) => 1 + (size a) + (size b)
  end.

Compute (size (Const 1)).
Compute (size (Plus (Const 1) (Times (Const 2) (Const 4)))).


Fixpoint depth (root: arith): nat :=
  match root with
  | Const _ | Var _ => 1
  | (Plus a b)|(Times a b) => 1 + (max (depth a) (depth b))
  end.

Compute (depth (Const 1)).
Compute (depth (Plus (Const 1) (Times (Const 2) (Const 4)))).
Compute (depth (Plus (Const 1) (Times (Plus (Const 2) (Const 3)) (Const 4)))).

Theorem depth_le_size: forall e,
  depth e <= size e.

Proof.
  intros e.
  induction e as [| | e1 IHe1 | e2 IHe2]; simpl; lia.
Qed.

Fixpoint commuter (root: arith): arith :=
  match root with
  | Plus a b => Plus (commuter b) (commuter a)
  | Times a b => Times (commuter b) (commuter a)
  | _ => root
  end.

Compute (commuter (Const 1)).
Compute (commuter (Plus (Const 1) (Times (Const 2) (Const 4)))).
Compute (commuter (Plus (Const 1) (Times (Plus (Const 2) (Const 3)) (Const 4)))).

Theorem size_commuter: forall e, size (commuter e) = size e.
Proof.
  induction e as [| | e1 IHe1 | e2 IHe2]; simpl; lia.
Qed.

Theorem depth_commuter: forall e, depth (commuter e) = depth e.
Proof.
  induction e as [| | e1 IHe1 | e2 IHe2]; simpl; lia.
Qed.

Theorem commuter_inverse: forall e, commuter (commuter e) = e.
Proof.
  induction e as [| | e1 IHe1 | e2 IHe2]; simpl; equality.
Qed.


Fixpoint substitute (orig: arith) (variable: var) (new_node: arith) : arith :=
  match orig with
  | Const _ => orig
  | Var x => if x =? variable then new_node else orig
  | Plus e1 e2 => Plus (substitute e1 variable new_node) (substitute e2 variable new_node)
  | Times e1 e2 => Times (substitute e1 variable new_node) (substitute e2 variable new_node)
  end.

Theorem substitute_depth : forall orig variable new_node,
      depth (substitute orig variable new_node)
      <= depth orig + depth new_node.
Proof.
  intros.
  induction orig as [| x | | ]; simpl; try lia.
  destruct (x =? variable) eqn: Heq; simpl; try lia.
Qed.


Theorem substitute_self : forall orig variable,
  substitute orig variable (Var variable) = orig.
Proof.
  intros. induction orig as [| x | | ]; simpl; try equality.
  destruct (x =? variable) eqn: Heq; try equality.
  - rewrite eqb_eq in Heq; rewrite Heq; reflexivity.
Qed.


Theorem substitute_commuter : forall orig variable new_node,
  commuter (substitute orig variable new_node)
= substitute (commuter orig) variable (commuter new_node).
Proof.
  intros. induction orig as [| x | | ]; simpl; try equality.
  destruct (x =? variable) eqn: Heq; try equality.
Qed.


Fixpoint eval (e: arith) (v: valuation) : nat :=
  match e with
  | Const n => n
  | Var x => match v x with
             | None => 0
             | Some n => n
             end
  | Plus e1 e2 => eval e1 v + eval e2 v
  | Times e1 e2 => eval e1 v * eval e2 v
  end.

Fixpoint eval_o (e: arith) (v: valuation) : option nat :=
  match e with
  | Const n => Some n
  | Var x => v x
  | Plus e1 e2 => match (eval_o e1 v), (eval_o e2 v) with
                  | None, _ => None
                  | _, None => None
                  | (Some n1), (Some n2) => Some (n1 + n1)
                  end
  | Times e1 e2 => match (eval_o e1 v), (eval_o e2 v) with
                  | None, _ => None
                  | _, None => None
                  | Some n1, Some n2 => Some (n1 * n1)
                   end
  end.


