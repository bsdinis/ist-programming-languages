From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition eq_string (x y: string) : bool :=
  if string_dec x y then true else false.

Theorem eq_string_refl: forall s: string, true = eq_string s s.
Proof.
  intros s.
  unfold eq_string.
  destruct (string_dec s s) as [Hs_eq | Hs_neq].
  - reflexivity.
  - destruct Hs_neq. reflexivity.
Qed.

Theorem eq_string_true_iff: forall x y: string, eq_string x y = true <-> x = y.
Proof.
  intros x y.
  unfold eq_string.
  destruct (string_dec x y) as [Hs_eq | Hs_neq].
  - rewrite Hs_eq. split; reflexivity.
  - split.
    -- intros contra. discriminate contra.
    -- intros H. exfalso. apply Hs_neq. apply H.
Qed.


Theorem eq_string_false_iff: forall x y: string, eq_string x y = false <-> x <> y.
Proof.
  intros x y.
  unfold eq_string.
  destruct (string_dec x y) as [Hs_eq | Hs_neq].
  - split.
    -- intros contra. discriminate contra.
    -- intros H. exfalso. apply H. apply Hs_eq.
  - split.
    -- intros contra. assumption.
    -- intros h. reflexivity.
Qed.

Definition total_map (A: Type) := string -> A.

Definition t_empty {A: Type} (v: A) : total_map A :=
  (fun _ => v).

Definition t_update {A: Type} (m:  total_map A) (x: string) (v: A) : total_map A:=
  fun y => if eq_string x y then v else m y.

Definition my_map : total_map nat := (t_update (t_empty 0) "k" 42).

Compute (my_map "a").
Compute (my_map "b").
Compute (my_map "k").


Notation "'_' '!->' v" := (t_empty v) (at level 100, right associativity).
Notation "x '!->' v ';' m" := (t_update m x v) (at level 100, v at next level, right associativity).

Definition my_map' :=
  ( "bar" !-> true;
    "foo" !-> true;
    _ !-> false
    ).

Compute my_map' "bar".
Compute my_map' "baz".
Compute my_map' "foo".

Lemma t_apply_empty: forall (A: Type) (x: string) (v: A),
  (_ !-> v) x = v.

Proof.  auto.  Qed.



Lemma t_update_eq: forall (A: Type) (m: total_map A) (x: string) (v: A),
  (x !-> v ; m) x = v.

Proof.
  intros.
  unfold t_update.
  rewrite <- eq_string_refl.
  reflexivity.
Qed.


Lemma t_update_neq: forall (A: Type) (m: total_map A) (x1 x2: string) (v: A),
  x1 <> x2 -> (x1 !-> v ; m) x2 = m x2.

Proof.
  intros A m x1 x2 v H.
  unfold t_update.
  apply eq_string_false_iff in H.
  rewrite -> H.
  reflexivity.
Qed.

Lemma if_else_if: forall (T: Type) (p: bool ) (v_if v_elif v_else: T),
  (if p then v_if else if p then v_elif else v_else) = (if p then v_if else v_else).

Proof.
  intros T p v_if v_elif v_else.
  destruct p; reflexivity.
Qed.


Lemma t_update_shadow: forall (A: Type) (m: total_map A) (x: string) (v1 v2: A),
  (x !-> v2 ; x !-> v1; m) = (x !-> v2 ; m).

Proof.
  intros A m x v1 v2.
  unfold t_update.
Admitted.


Lemma eq_stringP : forall x y : string,
    reflect (x = y) (eq_string x y).
Proof.
  intros x y.
Admitted.

Theorem t_update_same : forall (A : Type) (m : total_map A) x,
    (x !-> m x ; m) = m.
Proof.
  intros A m x.
  unfold t_update.
Admitted.
  

