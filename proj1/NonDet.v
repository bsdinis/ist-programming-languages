From Coq Require Import Lia.
From Coq Require Import Lists.List.
From Coq Require Import Arith.Arith.
From FirstProject Require Import Imp Maps.
From FirstProject Require Import Eval.
Import ListNotations.

(**
   We wish to prove several properties about the determinism of a program
   Summary:
     1. Programs without non-deterministic constructions are deterministic: `no_non_det`.
     2. Given a deterministic program c, c !! c is deterministic (and vice-versa): `non_det_of_same_det`.
     3. Given a deterministic program c1 !! c2, both c1 and c2 are deterministic: `deterministic_non_det_implies_det_clauses`.
     4. Given a deterministic program c1 !! c2, c1 and c2 are equivalent (and vice-versa): `det_non_det_forces_equivalence`.
 *)

(**
   An obvious question is how to define determinism.
   At first glance, a program is deterministic if all its executions result in a list of size one, always with the same value.
   However, in the case of programs with non_deterministic constructs (which may be deterministic nonetheless) the lists may have larger sizes.
   They must always be the same if the program is deterministic.
 *)
Definition is_det (c: com) : Prop :=
  forall st st1 st2,
  st =[ c ]=> st1 ->
  st =[ c ]=> st2 ->
  st1 = st2.


(**
   We may also define an equivalence property on programs.
   This property states that if two programs can transform the initial state st
   into the same final state st', they are equivalent
 *)
Definition are_equiv (c1 c2: com) : Prop :=
  forall st st',
  st =[ c1 ]=> st' <-> st =[ c2 ]=> st'.


(**
    We need to be able to assert that a program has no non-deterministic constructs
 *)
Fixpoint no_non_det_construct (c: com) : Prop :=
  match c with
  | CSkip => True
  | CAss _ _ => True
  | CSeq c1 c2 => (no_non_det_construct c1) /\ (no_non_det_construct c2)
  | CNonDet _ _ => False
  | CIf _ c1 c2 => (no_non_det_construct c1) /\ (no_non_det_construct c2)
  | CWhile _ c => (no_non_det_construct c)
  end.

(* We also prove several properties on this proposition:
    `no_non_det_seq` allows us to destruct a sequence;
    `no_non_det_if` allows us to destruct a if;
    `no_non_det_while` allows us to destruct a while;

   These make intiutive sense: if the overall expression does not have non-deterministic
   constructs, its parts won't have them as well.
    *)
Lemma no_non_det_seq: forall c1 c2,
  no_non_det_construct <{ c1; c2 }> -> no_non_det_construct c1 /\ no_non_det_construct c2.
Proof.
  intros c1 c2 H.
  split; unfold no_non_det_construct in H; destruct H as [H1 H2]; unfold no_non_det_construct; assumption.
Qed.

Lemma no_non_det_if: forall b c1 c2,
  no_non_det_construct <{ if b then c1 else c2 end }> -> no_non_det_construct c1 /\ no_non_det_construct c2.
Proof.
  intros b c1 c2 H.
  split; unfold no_non_det_construct in H; destruct H as [H1 H2]; unfold no_non_det_construct; assumption.
Qed.

Lemma no_non_det_while: forall b c,
  no_non_det_construct <{ while b do c end }> -> no_non_det_construct c.
Proof.
  intros b c H.
  unfold no_non_det_construct in H.
  unfold no_non_det_construct.
  assumption.
Qed.

(**
   This is the most trivial proof about determinism.
   If a program does not have any non-deterministic constructs, then it is deterministic
  *)
Theorem no_non_det: forall c,
  (no_non_det_construct c) ->
  is_det c.
Proof.
  intros c Hdet st st1 st2 E1 E2.
  generalize dependent st2.
  induction E1; intros st2 E2; inversion E2; subst; try contradiction.
  - (* E_Skip *) reflexivity.
  - (* E_Ass *) reflexivity.
  - (* E_Seq *)
    apply no_non_det_seq in Hdet.
    destruct Hdet as [Hdet1 Hdet2].
    specialize (IHE1_1 Hdet1).
    specialize (IHE1_2 Hdet2).
    rewrite (IHE1_1 st'0 H1) in *.
    apply IHE1_2. assumption.
  - (* E_IfTrue, b evaluates to true *)
    apply no_non_det_if in Hdet.
    destruct Hdet as [Hdet1 _].
    specialize (IHE1 Hdet1).
    apply IHE1. assumption.
  - (* E_IfTrue,  b evaluates to false (contradiction) *)
      rewrite H in H5. discriminate.
  - (* E_IfFalse, b evaluates to true (contradiction) *)
      rewrite H in H5. discriminate.
  - (* E_IfFalse, b evaluates to false *)
    apply no_non_det_if in Hdet.
    destruct Hdet as [_ Hdet2].
    specialize (IHE1 Hdet2).
    apply IHE1. assumption.
  - (* E_WhileFalse, b evaluates to false *)
    reflexivity.
  - (* E_WhileFalse, b evaluates to true (contradiction) *)
    rewrite H in H2. discriminate.
  - (* E_WhileTrue, b evaluates to false (contradiction) *)
    rewrite H in H4. discriminate.
  - (* E_WhileTrue, b evaluates to true *)
    specialize (IHE1_2 Hdet).
    apply no_non_det_while in Hdet.
    specialize (IHE1_1 Hdet).
    rewrite (IHE1_1 st'0 H3) in *.
    apply IHE1_2. assumption.
Qed.

(**
   We extend our proof about non-determinism.
   It is the case that if both branches of the
   non-deterministic construct are the same _deterministic_ program
   then the overall program is deterministic.
  *)
Lemma non_det_same_det: forall c,
  is_det c ->
  is_det <{ c !! c }>.
Proof.
    intros c H st st1 st2 H1 H2.
    unfold is_det in H.
    assert (st =[ c ]=> st1 -> st =[ c ]=> st2 -> st1 = st2). apply H.
    apply H0; apply choice_idempotent; assumption.
Qed.

(**
   We can prove the other direction as well.
   If a non-deterministic idempotent construct is deterministic,
   it must be the case that the inner program is deterministic.
 *)
Lemma same_det_non_det: forall c,
  is_det <{ c !! c }> ->
  is_det c.
Proof.
    intros c H st st1 st2 H1 H2.
    unfold is_det in H.
    assert (st =[ c !! c ]=> st1 -> st =[ c !! c ]=> st2 -> st1 = st2). apply H.
    apply H0; apply choice_idempotent; assumption.
Qed.

(**
   Stating equivalences is good for the soul.
 *)
Theorem non_det_of_same_det: forall c,
  is_det <{ c !! c }> <-> is_det c.
Proof.
  intros.
  split.
  - apply same_det_non_det.
  - apply non_det_same_det.
Qed.

(*
   A weaker version of this same_det_non_det states that if
   (for some reason) a non-deterministic construct is
   deterministic, then its clauses must also be deterministic.
 *)
Theorem deterministic_non_det_implies_det_clauses: forall c1 c2,
  is_det <{ c1 !! c2 }> ->
  (is_det c1 /\ is_det c2).
Proof.
    intros c1 c2 H_det_all.
    unfold is_det in *.
    split; intros st st1 st2 H1 H2;
    assert (st =[ c1 !! c2 ]=> st1 -> st =[ c1 !! c2 ]=> st2 -> st1 = st2) as H_det;
    try apply H_det_all.
    - apply H_det; apply E_NonDet1; assumption.
    - apply H_det; apply E_NonDet2; assumption.
Qed.

(**
   Here we can generalize the case where a non-deterministic construct
   is deterministic.

   For that to be true, both branches need to be deterministic (otherwise we would
   contradict `deterministic_non_det_implies_det_clauses`) and both programs
   must be equivalent, so no matter which branch is taken the effect is the same.
 *)
Lemma non_det_equiv_det: forall c1 c2,
  is_det c1 ->
  is_det c2 ->
  are_equiv c1 c2 ->
  is_det <{ c1 !! c2 }>.
Proof.
    intros c1 c2 H1_det_all H2_det_all H_eqv.
    unfold is_det in *.
    unfold are_equiv in H_eqv.
    intros st st1 st2 H1_non H2_non.
    assert (st =[ c1 ]=> st1 -> st =[ c1 ]=> st2 -> st1 = st2) as H1_det. apply H1_det_all.
    inversion H1_non; subst; inversion H2_non; subst;
    apply H1_det; try assumption; apply H_eqv; assumption.
Qed.

(**
   TODO: prove that if a non-deterministic construct is deterministic
   then both programs must be equivalent.
 *)
Lemma equiv_det_non_det: forall c1 c2,
  is_det <{ c1 !! c2 }> ->
  are_equiv c1 c2.
Proof.
    intros c1 c2 H_det_all.
    assert (is_det <{ c1 !! c2 }>) as H12_det_all. assumption.
    apply deterministic_non_det_implies_det_clauses in H12_det_all.
    destruct H12_det_all as [H1_det_all H2_det_all].
    unfold is_det in *.
    unfold are_equiv.
    intros st st'.
    split; intros H.
    admit.
Admitted.

(**
   Stating equivalences is good for the soul.
 *)
Theorem det_non_det_forces_equivalence: forall c1 c2,
  is_det <{ c1 !! c2 }> <-> (are_equiv c1 c2 /\ is_det c1 /\ is_det c2).
Proof.
  intros c1 c2.
  split.
  - intros H.
    split; try apply deterministic_non_det_implies_det_clauses; try assumption.
    apply equiv_det_non_det. assumption.
  - intros H.
    destruct H as [Heq H].
    destruct H as [H1 H2].
    apply non_det_equiv_det; assumption.
Qed.
