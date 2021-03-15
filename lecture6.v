Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.PeanoNat.


(* simplification *)

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

(* rewrite *)

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


(* case analysis *)

Definition beq_nat (a b: nat): bool := a =? b.

Theorem plus_1_neq_0_try: forall n: nat,
  beq_nat (n + 1) 0 = false.

Proof.
  intros n.
  simpl.
Abort. (* no simplification possible *)

Theorem plus_1_neq_0_try': forall n: nat,
  beq_nat (n + 1) 0 = false.

Proof.
  intros n.
  destruct beq_nat.  (* this destrubtion  considers that beq_nat can have two cases, true or false, so it will not work *)
Abort.


(* case by case analysis *)
Theorem plus_1_neq_0: forall n: nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n.
  destruct n.

  (* case 1: n = 0 *)
  reflexivity.

  (* case 2: n = S n' *)
  reflexivity.
Qed.

Theorem plus_1_neq_0': forall n: nat,
  beq_nat (n + 1) 0 = false.

(* better syntax *)
Proof.
  intros n.
  destruct n.
  - reflexivity.
  - reflexivity.
Qed.


(* bind name to destructed *)
Theorem plus_1_neq_0'': forall n: nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n.
  destruct n as [| n'].
  - reflexivity.
  - reflexivity.
Qed.

(* if the tactic for both cases is the same, present the tactic *)
Theorem plus_1_neq_0''': forall n: nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n.
  destruct n; reflexivity.
Qed.


(* another destruction *)
Theorem negb_involutive: forall b: bool,
  negb( negb b) = b.
Proof.
  intros b.
  destruct b; reflexivity.
Qed.

(* nested destructs: different bullest: -, +, * *)
Theorem andb_commutative: forall a b, andb a b = andb b a.
Proof.
  intros a b.
  destruct a.
  - destruct b.
    + reflexivity.
    + reflexivity.
  - destruct b.
    + reflexivity.
    + reflexivity.
Qed.

(* nested destructs : curly braces *)
Theorem andb_commutative': forall a b, andb a b = andb b a.
Proof.
  intros a b.
  destruct a.
  { destruct b.
    { reflexivity. }
    { reflexivity. } }
  { destruct b.
    { reflexivity. }
    { reflexivity. } }
Qed.


(* we know better *)
Theorem andb_commutative'': forall a b, andb a b = andb b a.
Proof.
  intros a b.
  destruct a; destruct b; reflexivity.
Qed.

(* simultaneous introduction and destruction *)
Theorem plus_1_neq_0'''': forall n: nat,
  beq_nat (n  + 1) 0 = false.

Proof.
  intros [|n]; reflexivity.
Qed.

(* simultaneous introduction and destruction with anonymous names *)
Theorem andb_commutative''': forall a b, andb a b = andb b a.
Proof.
  intros [] []; (* introduce two anonymous names and destruct them. this is OK because we don't refer to the generated names in the proof *)
  reflexivity; reflexivity.
Qed.

(* simultaneous introduction and destruction with anonymous names: explicit tactics *)
Theorem andb_commutative'''': forall a b, andb a b = andb b a.
Proof.
  intros [] []. (* introduce two anonymous names and destruct them. this is OK because we don't refer to the generated names in the proof *)
   - reflexivity.
   - reflexivity.
   - reflexivity.
   - reflexivity.
Qed.


(* exercises *)

Theorem andb_true_elim2: forall a b: bool,
  andb a b = true -> b = true.
Proof.
  intros a b.
  destruct b.
  - reflexivity.
  - destruct a; simpl; intros H; rewrite H; reflexivity.
Qed.

Theorem zero_nbeq_plus_1: forall n: nat,
  beq_nat 0 (n + 1) = false.
Proof.
  intros [|n]; simpl; reflexivity.
Qed.

(* induction *)

Theorem plus_n_0_try: forall n: nat, n = n + 0.
Proof.
  intros n.
  simpl.
Abort.

(* induction destructs the goal in the goal of the base case and a Hypothesis based goal *)
Theorem plus_n_0: forall n: nat, n = n + 0.
Proof.
  intros n.
  induction n as [|n' IHn']; simpl.
  - reflexivity.
  - rewrite <- IHn'. reflexivity.
Qed.

(* exercises *)

Theorem mult_0_r: forall n: nat,
  n * 0 = 0.
Proof.
  intros n.
  induction n as [|n' IHn']; simpl.
  - reflexivity.
  - rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_n_Sm: forall n m: nat,
  S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [|n IHn]; simpl.
  - reflexivity.
  - rewrite <- IHn. reflexivity.
Qed.

Theorem plus_comm: forall n m: nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n as [|n IHn]; simpl.
  - rewrite <- plus_n_0. reflexivity.
  - rewrite -> IHn. rewrite plus_n_Sm. reflexivity.
Qed.


Theorem plus_assoc: forall n m o: nat,
  n + (m + o) = (n + m) + o.
Proof.
  intros n m o.
  induction n as [|n IHn]; simpl.
  - reflexivity.
  - rewrite -> IHn. reflexivity.
Qed.


(* proofs on user defined functions *)
Fixpoint double (n: nat) :=
  match n with
  | 0 => 0
  | S n' => S (S (double n'))
  end.

Lemma double_plus: forall n, double n = n + n.
Proof.
  intros n.
  induction n as [|n IH]; simpl.
  - reflexivity.
  - rewrite -> IH. rewrite plus_n_Sm. reflexivity.
Qed.


(* assumption *)
Theorem p_implies_p: forall P: Prop,
  P -> P.
Proof.
  intros P H.
  assumption. (* we do this when our goal is an hypothesis *)
Qed.


(* unfold : rewrite with the definition *)
Definition inc(n: nat) : nat := n + 1.
Lemma foo_defn: forall n, inc n = S n.
Proof.
  intros n.
  unfold inc.
  rewrite <- plus_n_Sm.
  rewrite <- plus_n_0.
  reflexivity.
Qed.

(* ring: ring arithmetic (Set, +, * ) with associativity, commutativity and distribution *)
Require Import Arith.
Theorem foil: forall a b c d,
  (a + b) * (c + d) = a * c + a * d + b * c + b * d.
Proof.
  intros. ring.
Qed.
