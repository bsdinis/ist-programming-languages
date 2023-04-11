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
  | Minus (a b: arith)
  | Plus (a b: arith)
  | Times (a b: arith).


Fixpoint size (root: arith) :  nat :=
  match root with
  | Const _ | Var _ => 1
  | (Minus a b)|(Plus a b)|(Times a b) => 1 + (size a) + (size b)
  end.

Compute (size (Const 1)).
Compute (size (Plus (Const 1) (Times (Const 2) (Const 4)))).


Fixpoint depth (root: arith): nat :=
  match root with
  | Const _ | Var _ => 1
  | (Minus a b)|(Plus a b)|(Times a b) => 1 + (max (depth a) (depth b))
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

Fixpoint commuter (root: arith): arith :=
  match root with
  | Minus a b => Minus (commuter b) (commuter a)
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


Fixpoint substitute (orig: arith) (variable: var) (new_node: arith) : arith :=
  match orig with
  | Const _ => orig
  | Var x => if x =? variable then new_node else orig
  | Minus e1 e2 => Minus (substitute e1 variable new_node) (substitute e2 variable new_node)
  | Plus e1 e2 => Plus (substitute e1 variable new_node) (substitute e2 variable new_node)
  | Times e1 e2 => Times (substitute e1 variable new_node) (substitute e2 variable new_node)
  end.

Theorem substitute_depth : forall orig variable new_node,
      depth (substitute orig variable new_node)
      <= depth orig + depth new_node.
Proof.
  intros.
  induction orig as [| x | | | ]; simpl; try lia.
  destruct (x =? variable); simpl; try lia.
Qed.


Theorem substitute_self : forall orig variable,
  substitute orig variable (Var variable) = orig.
Proof.
  intros. induction orig as [| x | | | ]; simpl; try equality.
  destruct (x =? variable) eqn: Heq; try equality.
  - rewrite eqb_eq in Heq; rewrite Heq; reflexivity.
Qed.


Theorem substitute_commuter : forall orig variable new_node,
  commuter (substitute orig variable new_node)
= substitute (commuter orig) variable (commuter new_node).
Proof.
  intros. induction orig as [| x | | | ]; simpl; try equality.
  destruct (x =? variable) eqn: Heq; try equality.
Qed.


Fixpoint eval (e: arith) (v: valuation) : nat :=
  match e with
  | Const n => n
  | Var x => match v x with
             | None => 0
             | Some n => n
             end
  | Minus e1 e2 => eval e1 v - eval e2 v
  | Plus e1 e2 => eval e1 v + eval e2 v
  | Times e1 e2 => eval e1 v * eval e2 v
  end.

Fixpoint eval_o (e: arith) (v: valuation) : option nat :=
  match e with
  | Const n => Some n
  | Var x => v x
  | Minus e1 e2 => match (eval_o e1 v), (eval_o e2 v) with
                  | None, _ => None
                  | _, None => None
                  | (Some n1), (Some n2) => Some (n1 - n1)
                  end
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


Inductive cmd :=
  | Skip
  | Assign (x: var) (e: arith) (* let x = e *)
  | Sequence (c1 c2: cmd) (* c1; c2 *)
  | Repeat (r: arith) (body: cmd).

(* f^n (x) == f f f f ... f (x) [n times] *)
Fixpoint self_compose {T} (f: T -> T) (n: nat) : T -> T :=
  match n with
  | 0 => (fun x => x)
  | S n' => (fun x => (f ((self_compose f n') x)))
  end.

Fixpoint exec (c: cmd) (v: valuation) : valuation :=
  match c with
  | Skip => v
  | Assign x e => x |-> (eval e v); v
  | Sequence c1 c2 => exec c2 (exec c1 v)
  | Repeat e body => (self_compose (exec body) (eval e v)) v
  end.

Coercion Const : nat >-> arith.
Coercion Var : var >-> arith.
Infix "+" := Plus : arith_scope.
Infix "-" := Minus : arith_scope.
Infix "*" := Times : arith_scope.
Delimit Scope arith_scope with arith.
Notation "x <- e" := (Assign x e%arith) (at level 75).
Infix ";" := Sequence (at level 76).
Notation "'repeat' e 'doing' body 'done'" := (Repeat e %arith body) (at level 75).

Lemma cmd_seq_assoc: forall c1 c2 c3 v,
    exec ((c1 ; c2 ) ; c3) v = exec (c1 ; (c2 ; c3)) v.
Proof.
  intros. reflexivity.
Qed.


Lemma cmd_seq_skip_r: forall c v,
    exec (c ; Skip) v = exec c v.
Proof.
  intros. reflexivity.
Qed.

Lemma cmd_seq_skip_l: forall c v,
    exec (Skip ; c) v = exec c v.
Proof.
  intros. reflexivity.
Qed.

Lemma cmd_no_repeat: forall c v,
    exec (repeat 0 doing c done) v = exec Skip v.
Proof.
  intros. reflexivity.
Qed.

Lemma cmd_repeat_unroll: forall c1 v (n:nat),
          exec (repeat (n+1) doing c1 done) v
        = exec (c1; repeat n doing c1 done) v.
Proof.
  intros.
  simpl.
  induction n as [| n' IHn] ; simpl; try reflexivity.
  - rewrite -> IHn. reflexivity.
Qed.


Fixpoint seqself (c : cmd) (n : nat) : cmd :=
  match n with
  | O => Skip
  | S n' => Sequence c (seqself c n')
  end.

Fixpoint unroll (c : cmd) : cmd :=
  match c with
  | Skip => c
  | Assign _ _ => c
  | Sequence c1 c2 => Sequence (unroll c1) (unroll c2)
  | Repeat (Const n) c1 => seqself (unroll c1) n
  | Repeat e c1 => Repeat e (unroll c1)
  end.

Example counter :=
  "output" <- 0;
  repeat 3 doing
      "output" <- "output" + 1
  done.

Example unrolled_counter :=
  "output" <- 0;
  "output" <- "output" + 1;
  "output" <- "output" + 1;
  "output" <- "output" + 1.

Compute unroll counter.


Lemma self_compose_extensional : forall {A} (f g : A -> A) n x,
    (forall y, f y = g y)
    -> self_compose f n x = self_compose g n x.
Proof.
Admitted.


Lemma seqself_ok : forall c n v,
    exec (seqself c n) v = self_compose (exec c) n v.
Proof.
Admitted.

Lemma exec_equiv: forall c1 c2 v,
  (exec c1 v = exec c2 v) -> (c1 = c2).
Proof.
Admitted.

Theorem unroll_ok : forall c v, exec (unroll c) v = exec c v.
Proof.
  intros.
  induction c as [ | | c1 IHc1 c2 IHc2 | r IHr c IHc ]; try reflexivity.
Admitted.

