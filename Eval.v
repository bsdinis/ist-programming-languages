From Coq Require Import Lia.
From Coq Require Import Lists.List.
From Coq Require Import Arith.Arith.
From FirstProject Require Import Imp Maps.
Import ListNotations.

(* 3.1. DONE: Change/extend ceval_step as specified *)

Notation "'LETOPT' st <== e1 'IN' e2"
   := (match e1 with
         | Some st => e2
         | None => None
       end)
   (right associativity, at level 60).

Fixpoint foreach_state
  (states: list (option state))
  (c2: com)
  (i: nat)
  (eval: state -> com -> nat -> list (option state))
  : list (option state) :=
  match states with
  | [] => []
  | (Some h)::tail => (eval h c2 i) ++ (foreach_state tail c2 i eval)
  | None::tail => None::(foreach_state tail c2 i eval)
  end.

Check option_map.
Compute (option_map S (Some(0))).
Compute (option_map S None).
Check map.

Fixpoint flat_option_map {A B: Type} (f: A -> (list (option B))) (l1: list (option A)) :=
  match l1 with
  | [] => []
  | h::t => match h with
            | None => None::(flat_option_map f t)
            | Some a => (f a) ++ (flat_option_map f t)
            end
  end.


Fixpoint ceval_step (st : state) (c : com) (i : nat)
                    : list (option state) :=
  match i with
  | O => [None]
  | S i' =>
    match c with
      | <{ skip }> =>
          [Some st]
      | <{ l := a1 }> =>
          [Some (l !-> aeval st a1 ; st)]
      | <{ c1 ; c2 }> => (flat_option_map (fun st' => (ceval_step st' c2 i')) (ceval_step st c1 i'))
      | <{ c1 !! c2 }> => (ceval_step st c1 i') ++ (ceval_step st c2 i')
      | <{ if b then c1 else c2 end }> =>
          if (beval st b)
            then ceval_step st c1 i'
            else ceval_step st c2 i'
      | <{ while b1 do c1 end }> =>
         if (beval st b1)
          then (flat_option_map (fun st' => (ceval_step st' c i')) (ceval_step st c1 i'))
          else [Some st]
    end
  end.

(* ################################################################# *)
(** * Relational vs. Step-Indexed Evaluation *)

(* 3.2. TODO: Prove ceval_step__ceval, ceval_step_more,
	ceval__ceval_step, and ceval_and_ceval_step_coincide
	(for the new implementation of the step-indexed evaluator) *)

(* (ceval_step st_i c2 i) C (ceval_step st c1;c2 (S i)) *)

Lemma in_flat_map: forall c st i l1 l2 st_contained,
  In st_contained (ceval_step st c i) ->
  In st_contained (flat_option_map (fun st' => (ceval_step st' c i)) l1++(Some st)::l2).
Proof.
  intros.
Admitted.

Lemma middle_state_exists: forall c1 c2 st st' i,
  In (Some st') (ceval_step st <{c1 ; c2}> (S i)) ->
    (exists st_i, In (Some st_i) (ceval_step st c1 i) /\ In (Some st') (ceval_step st_i c2 i) ).
Proof.
  intros c1 c2 st st' i H.
  simpl in H.
  destruct (ceval_step st c1 i).
  - contradiction.
  -
    destruct flat_option_map in H.
    -- contradiction.
Admitted.

Lemma middle_state_exists': forall c1 c2 st st',
  st =[ c1; c2 ]=> st' ->
  (exists st_i, st =[ c1 ]=> st_i /\ st_i =[ c2 ]=> st').
Proof.
Admitted.

(**
   If there is a branch of computation (defined by the step-index evaluator)
   that transforms st in st', there is a corresponding relational evaluation
   that transforms st in st'.
 *)
Theorem ceval_step__ceval: forall c st st',
      (exists i, In (Some st') (ceval_step st c i)) ->
      st =[ c ]=> st'.
Proof.
  intros c st st' H.

  (* remove exists from premise
      this way we can handle a concrete (but generalized) case*)
  inversion H as [i H_in]; subst.
  clear H.
  generalize dependent st'.
  generalize dependent st.
  generalize dependent c.

  (* induction on step *)
  induction i as [| i' Hi' ].
  - (* i == 0 *)
    intros c st st' H. simpl in H. destruct H; try discriminate; try contradiction.
  - (* i == S i' *)
    intros c st st' H.
    destruct c; simpl in H.
    -- (* skip *)
       destruct H as [H_Some | H_False]; try contradiction; simpl.
       inversion H_Some as [H_state].
       apply E_Skip.
    -- (* := *)
       destruct H. inversion H as [H_aeval].
       --- destruct H. apply E_Ass. reflexivity.
       --- contradiction.

    -- (* ; *)
       apply E_Seq.
       (*
       --- destruct (ceval_step st c1 i') eqn:Heqr1.
           + contradiction.
           + destruct flat_option_map.
             ++ contradiction.
             ++ apply Hi'. apply (middle_state_exists  _ _ _  _ i').
       --- apply Hi'.
       --- destruct flat_option_map.
         + contradiction.
         + destruct H.
            ++ admit.
            ++ admit. *)

    -- (* !! *)
       apply in_app_or in H. apply E_NonDet. destruct H.
       + (* left *) left. apply Hi'. assumption.
       + (* right *) right. apply Hi'. assumption.

    -- (* if *)
       destruct (beval st b) eqn:Heqr.
       + (* r = true *)
         apply E_IfTrue. rewrite Heqr. reflexivity.
         apply Hi'. assumption.
       + (* r = false *)
         apply E_IfFalse. rewrite Heqr. reflexivity.
         apply Hi'. assumption.

    -- (* while *)
      destruct (beval st b) eqn :Heqr.
      --- (* r = true *)
        destruct (ceval_step st c i') eqn:Heqr1.
        + (* [] *) contradiction.
        + (* head::tail *) apply E_WhileTrue with st'; try assumption.
          ++
            destruct flat_option_map.
              +++ contradiction.
              +++
                admit.
          ++
            destruct flat_option_map.
              +++ contradiction.
              +++
                apply Hi'.
                admit.
      --- (* r = false *)
        destruct H.
          + injection H as H2. rewrite <- H2. apply E_WhileFalse. apply Heqr.
          + contradiction.

Admitted.

Theorem ceval_step_more: forall i1 i2 st st' c,
  i1 <= i2 ->
  In (Some st') (ceval_step st c i1) ->
  In (Some st') (ceval_step st c i2).
Proof.
  induction i1 as [|i1']; intros i2 st st' c Hle Hceval.
  - (* i1 = 0 *)
    simpl in Hceval. destruct Hceval; try contradiction; try discriminate.
  - (* i1 = S i1' *)
    destruct i2 as [|i2']. inversion Hle.
    assert (Hle': i1' <= i2') by lia.
    destruct c.
    -- (* skip *)
       simpl in Hceval. simpl. assumption.
    -- (* := *)
       simpl in Hceval. simpl. assumption.

    -- (* ; *)
       simpl in Hceval. simpl.
       destruct (ceval_step st c1 i1') eqn:Heqst1'o.
       --- contradiction.
       --- destruct (ceval_step st c1 i2').
            + admit.
            + admit.
    -- (* !! *)
        simpl in Hceval. simpl. apply in_app_or in Hceval. apply in_app_iff.
        destruct Hceval.
        + left. apply IHi1'; assumption.
        + right. apply IHi1'; assumption.

    -- (* if *)
       simpl in Hceval. simpl.
       destruct (beval st b) ; apply IHi1'; assumption.
    -- (* while *)
       admit.
Admitted.

(* ceval_step_more can be used in the proof of ceval__ceval_step *)
Theorem ceval__ceval_step: forall c st st',
      st =[ c ]=> st' ->
      exists i, In (Some st') (ceval_step st c i).
Proof.
    intros c st st' Hce.
    induction Hce.
    - (* skip *)
      assert (In (Some st) (ceval_step st <{ skip }> 1)).
      + simpl. left. reflexivity.
      + eexists. apply H.
    - (* := *)
      assert (In (Some (x !-> n; st)) (ceval_step st <{ x := a }> 1)).
      + simpl. left. rewrite H. reflexivity.
      + eexists. apply H0.
    - (* ; *)
      destruct IHHce1 as [i1 H1]. destruct IHHce2 as [i2 H2].
      admit.
    - (* !! *)
      destruct H.
      + (* st =[ c1 ]=> st' *)
        admit.
      + (* st =[ c2 ]=> st' *)
        admit.
    - (* if true *)
      admit.
    - (* if false *)
      admit.
    - (* while false *)
      admit.
    - (* while true *)
      admit.
Admitted.

Theorem ceval_and_ceval_step_coincide: forall c st st',
      st =[ c ]=> st'
  <-> exists i, In (Some st') (ceval_step st c i).
Proof.
  intros.
  split.
  - apply ceval__ceval_step.
  - apply ceval_step__ceval.
Qed.
