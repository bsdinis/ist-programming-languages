Load Maps.
Load TacticsLP.

Notation var := string.
Definition valuation := partial_map nat.

Example m1 := "x" |-> 0.
Compute (m1 "x").
Compute (m1 "v").

Example m2 := "x" |-> 1; m1.
Compute (m2 "x").
Compute (m2 "v").

Inductive arith: Type :=
  | Const (n: nat)
  | Var (x: var)
  | Plus (e1 e2: arith)
  | Minus (e1 e2: arith)
  | Times (e1 e2: arith).

Example ex1 := Const 42.
Example ex2 := Plus (Var "y") (Times (Var "x") (Const 3)).

Fixpoint interp (e: arith) (v: valuation) : nat :=
  match e with
  | Const n => n
  | Var x => match v x with
             | None => 0
             | Some n => n
             end
  | Plus e1 e2 => interp e1 v + interp e2 v
  | Minus e1 e2 => interp e1 v - interp e2 v
  | Times e1 e2 => interp e1 v * interp e2 v
  end.

Definition valuation0:  valuation := "x" |-> 17; "y" |-> 3.

Compute interp ex1 valuation0.
Compute interp ex2 valuation0.

Fixpoint substitute (orig: arith) (pattern: var) (new_node: arith) : arith :=
  match orig with
  | Const _ => orig
  | Var x => if x =? pattern then new_node else orig
  | Plus e1 e2 => Plus (substitute e1 pattern new_node) (substitute e2 pattern new_node)
  | Minus e1 e2 => Minus (substitute e1 pattern new_node) (substitute e2 pattern new_node)
  | Times e1 e2 => Times (substitute e1 pattern new_node) (substitute e2 pattern new_node)
  end.


(* substituting is the same as adding a new mapping to the binding map *)
Theorem substitute_ok: forall v pattern new_node orig,
  interp (substitute orig pattern new_node) v = interp orig (pattern |-> interp new_node v ; v).

Proof.
  induction orig; simpl; try equality.
  cases (x =? pattern).
  - rewrite eqb_eq in Heq. rewrite Heq. rewrite update_eq. reflexivity.
  - rewrite eqb_neq in Heq. rewrite update_neq. simpl. reflexivity. apply not_eq_sym. assumption.
Qed.

Fixpoint bad_constant_folding (e: arith) : arith :=
  match e with
  | Const _ | Var _ => e
  | Plus (Const n1) (Const n2) => Const (n1 + n2)
  | Plus e1 e2 => Plus (bad_constant_folding e1) (bad_constant_folding e2)
  | Minus (Const n1) (Const n2) => Const (n1 - n2)
  | Minus e1 e2 => Minus (bad_constant_folding e1) (bad_constant_folding e2)
  | Times (Const n1) (Const n2) => Const (n1 * n2)
  | Times e1 e2 => Times (bad_constant_folding e1) (bad_constant_folding e2)
  end.

Fixpoint constant_folding (e: arith) : arith :=
  match e with
  | Const _ | Var _ => e
      (* we need to do constant folding on the leaves and then on the parent (if we have a lot of constants,
         we'll do everything *)
  | Plus e1 e2  => match (constant_folding e1), (constant_folding e2) with
                   | (Const n1), (Const n2) => Const (n1 + n2)
                   | e1',  e2' => (Plus e1' e2')
                   end
  | Minus e1 e2  => match (constant_folding e1), (constant_folding e2) with
                   | (Const n1), (Const n2) => Const (n1 - n2)
                   | e1',  e2' => (Minus e1' e2')
                   end
  | Times e1 e2  => match (constant_folding e1), (constant_folding e2) with
                   | (Const n1), (Const n2) => Const (n1 * n2)
                   | e1',  e2' => (Times e1' e2')
                   end
  end.

Definition is_constant (e: arith) : bool :=
  match e with
  | Const _ => true
  | _ => false
  end.


Definition ast := Plus (Var "y") (Times (Plus (Const 1) (Const 2)) (Minus (Const 10) (Const 3))).
Compute bad_constant_folding ast.
Compute constant_folding ast.

Theorem bad_constant_folding_ok : forall e v,
  interp (bad_constant_folding e) v = interp e v.

Proof.
  induction e as [| | e1 IHe1 e2 IHe2 | e1 IHe1 e2 IHe2 | e1 IHe1 e2 IHe2 ]; simpl; try equality; intros; simpl; rewrite <- IHe1; rewrite <- IHe2.
  - cases e1; simpl; try equality.
    cases e2; simpl; try equality.
  - cases e1; simpl; try equality.
    cases e2; simpl; try equality.
  - cases e1; simpl; try equality.
    cases e2; simpl; try equality.
Qed.


Theorem constant_folding_ok : forall e v,
  interp (constant_folding e) v = interp e v.

Proof.
  induction e; simpl; try equality; intros;
  destruct (constant_folding e1) eqn:Heq1; destruct (constant_folding e2) eqn:Heq2; rewrite <- IHe1; rewrite <- IHe2; equality.
Qed.

