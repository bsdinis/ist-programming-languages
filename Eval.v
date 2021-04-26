From Coq Require Import Lia.
From Coq Require Import Lists.List.
From Coq Require Import Arith.Arith.
From FirstProject Require Import Imp Maps.
Import ListNotations.

(* 3.1. DONE: Change/extend ceval_step as specified *)

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
      | <{ c1 ; c2 }> => (
        flat_map (fun opt_st' => (match opt_st' with
                                  | None => [None]
                                  | Some st' => ceval_step st' c2 i'
                                  end)
        ) (ceval_step st c1 i')
      )
      | <{ c1 !! c2 }> => (ceval_step st c1 i') ++ (ceval_step st c2 i')
      | <{ if b then c1 else c2 end }> =>
          if (beval st b)
            then ceval_step st c1 i'
            else ceval_step st c2 i'
      | <{ while b1 do c1 end }> =>
         if (beval st b1)
          then (
            flat_map (fun opt_st' => (match opt_st' with
                                      | None => [None]
                                      | Some st' => ceval_step st' c i'
                                      end)
            ) (ceval_step st c1 i')
          )
          else [Some st]
    end
  end.

(* ################################################################# *)
(** * Relational vs. Step-Indexed Evaluation *)

(* 3.2. DONE: Prove ceval_step__ceval, ceval_step_more,
	ceval__ceval_step, and ceval_and_ceval_step_coincide
	(for the new implementation of the step-indexed evaluator) *)

(* This is useful to introduce the intermediate state in a sequence
 *)
Lemma seq_middle_state_exists: forall c1 c2 st st' i,
  In (Some st') (ceval_step st <{c1 ; c2}> (S i)) <->
    (exists st_i, In (Some st_i) (ceval_step st c1 i) /\ In (Some st') (ceval_step st_i c2 i) ).
Proof.
  intros c1 c2 st st' i.
  split.
  - intros H.
    simpl in H.
    apply in_flat_map in H.
    destruct H.
    destruct H as [H_x_in].
    destruct x.
    -- eexists.
      split.
      --- apply H_x_in.
      --- apply H.
    -- simpl in H.
        destruct H.
      --- inversion H.
      --- contradiction.
  - intros H.
    destruct H as [st_i H].
    destruct H as [H1 H2].
    simpl.
    apply in_flat_map.
    eexists.
    split.
    -- apply H1.
    -- apply H2.
Qed.

(* This is useful to introduce the intermediate state after a run of a  while loop
 *)
Lemma while_middle_state_exists: forall b c st st' i,
  beval st b = true ->
  (In (Some st') (ceval_step st <{ while b do c end}> (S i)) <->
    (exists st_i, In (Some st_i) (ceval_step st c i) /\ In (Some st') (ceval_step st_i <{ while b do c end}> i) )).
Proof.
  intros b c st st' i Hb.
  split.
  - intros H.
    simpl in H.
    rewrite Hb in H.
    apply in_flat_map in H.
    destruct H.
    destruct H as [H_x_in].
    destruct x.
    -- eexists.
      split.
      --- apply H_x_in.
      --- apply H.
    -- simpl in H.
      destruct H.
      --- inversion H.
      --- contradiction.
  - intros H.
    destruct H as [st_i H].
    destruct H as [H1 H2].
    simpl.
    rewrite Hb.
    apply in_flat_map.
    eexists.
    split.
    -- apply H1.
    -- apply H2.
Qed.

(**
   If there is a branch of computation (defined by the step-index evaluator)
   that transforms st in st', there is a corresponding relational evaluation
   that transforms st in st'.

   In other words, the step-index evaluator ''implies'' the relational evaluator
   (meaning that all computations in the step-index evaluator have a matching relational evaluation)

   This property, in conjunction with ceval__ceval_step, proves the equivalence of the evaluators.
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
    destruct c.
    -- (* skip *)
       destruct H as [H_Some | H_False]; try contradiction; simpl.
       inversion H_Some as [H_state].
       apply E_Skip.
    -- (* := *)
       destruct H. inversion H as [H_aeval].
       --- destruct H. apply E_Ass. reflexivity.
       --- contradiction.

    -- (* ; *)
      apply seq_middle_state_exists in H.
      destruct H.
      destruct H as [H1 H2].
      apply Hi' in H1.
      apply Hi' in H2.
      apply E_Seq with x; assumption.
    -- (* !! *)
       apply in_app_or in H. destruct H.
       --- apply E_NonDet1. apply Hi'. assumption.
       --- apply E_NonDet2. apply Hi'. assumption.
    -- (* if *)
       destruct (beval st b) eqn:Heqr.
       --- (* r = true *)
         apply E_IfTrue. rewrite Heqr. reflexivity.
         unfold ceval_step in H.
         rewrite Heqr in H.
         apply Hi'. assumption.
       --- (* r = false *)
         apply E_IfFalse. rewrite Heqr. reflexivity.
         unfold ceval_step in H.
         rewrite Heqr in H.
         apply Hi'. assumption.

    -- (* while *)
      destruct (beval st b) eqn :Hguard.
      --- (* r = true *)
          apply while_middle_state_exists in H; try assumption.
          destruct H.
          destruct H as [H1 H2].
          apply Hi' in H1.
          apply Hi' in H2.
          apply E_WhileTrue with x; assumption.
      --- (* r = false *)
        simpl in H.
        rewrite Hguard in H.
        simpl in H.
        destruct H.
        ---- injection H as H2. rewrite <- H2. apply E_WhileFalse. apply Hguard.
        ---- contradiction.
Qed.

(**
   If we give more gas to a computation, it will produce _at least_ the same results.
 *)
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
       simpl in Hceval.
       apply seq_middle_state_exists in Hceval.
       apply seq_middle_state_exists.
       destruct Hceval as [x Hceval].
       destruct Hceval as [H1 H2].
       apply (IHi1' (i2') _ _ _ ) in H1 ; try lia.
       apply (IHi1' (i2') _ _ _ ) in H2 ; try lia.
       eexists.
       split.
       --- apply H1.
       --- apply H2.
    -- (* !! *)
        simpl in Hceval. simpl. apply in_app_or in Hceval. apply in_app_iff.
        destruct Hceval.
        --- left. apply IHi1'; assumption.
        --- right. apply IHi1'; assumption.
    -- (* if *)
       simpl in Hceval. simpl.
       destruct (beval st b) ; apply IHi1'; assumption.
    -- (* while *)
       (* simpl in Hceval *)
       destruct (beval st b) eqn:Hguard.
       --- (* guard is true *)
           apply while_middle_state_exists in Hceval; try assumption.
           apply while_middle_state_exists; try assumption.
           destruct Hceval as [st_i Hceval].
           destruct Hceval as [H1 H2].
           apply (IHi1' (i2') _ _ _ ) in H1 ; try lia.
           apply (IHi1' (i2') _ _ _ ) in H2 ; try lia.
           eexists.
           split.
           ---- apply H1.
           ---- apply H2.
       --- (* guard is false *)
           simpl in Hceval.
           simpl.
           rewrite Hguard in Hceval.
           rewrite Hguard.
           assumption.
Qed.

(**
   If there is a relational evaluation of a program, there will be a matching
   evaluation in the step-index evaluator, for some ammount of gas i.

   In other words, the relational evaluator ''implies'' the step-index evaluator
   (meaning that all computations in the relational evaluator have a matching step-index evaluation)

   This property, in conjunction with ceval_step__ceval, proves the equivalence of the evaluators.
 *)
Theorem ceval__ceval_step: forall c st st',
      st =[ c ]=> st' ->
      exists i, In (Some st') (ceval_step st c i).
Proof.
    intros c st st' Hce.
    induction Hce.
    - (* skip *)
      assert (In (Some st) (ceval_step st <{ skip }> 1)).
      -- simpl. left. reflexivity.
      -- eexists. apply H.
    - (* := *)
      assert (In (Some (x !-> n; st)) (ceval_step st <{ x := a }> 1)) as Hin.
      -- simpl. left. rewrite H. reflexivity.
      -- eexists. apply Hin.
    - (* ; *)
      destruct IHHce1 as [i1 IHc1].
      destruct IHHce2 as [i2 IHc2].
      remember (max i1 i2) as i_max.
      apply (ceval_step_more i1 i_max _ _ _) in IHc1; try lia.
      apply (ceval_step_more i2 i_max _ _ _) in IHc2; try lia.
      eexists.
      apply seq_middle_state_exists.
      eexists.
      split.
      -- apply IHc1.
      -- apply IHc2.
    - (* !! (1) *)
      destruct IHHce as [i IH].
      assert (In (Some st') (ceval_step st <{ c1 !! c2 }> (S i))) as H.
      -- simpl. apply in_app_iff. left. assumption.
      -- eexists. apply H.
    - (* !! (2) *)
      destruct IHHce as [i IH].
      assert (In (Some st') (ceval_step st <{ c1 !! c2 }> (S i))) as H.
      -- simpl. apply in_app_iff. right. assumption.
      -- eexists. apply H.
    - (* if true *)
      destruct IHHce as [i IHc1].
      assert ((ceval_step st c1 i) = (ceval_step st <{ if b then c1 else c2 end }> (S i))).
      -- simpl. rewrite H. reflexivity.
      -- eexists. rewrite <- H0. assumption.
    - (* if false *)
      destruct IHHce as [i IHc2].
      assert ((ceval_step st c2 i) = (ceval_step st <{ if b then c1 else c2 end }> (S i))) as Heq.
      -- simpl. rewrite H. reflexivity.
      -- eexists. rewrite <- Heq. assumption.
    - (* while false *)
      assert ((ceval_step st <{skip}> 1) = (ceval_step st <{ while b do c end }> 2)) as Heq.
      -- simpl. rewrite H. reflexivity.
      -- eexists. rewrite <- Heq. simpl. left. reflexivity.
    - (* while true *)
      destruct IHHce1 as [i1 IHc1].
      destruct IHHce2 as [i2 IHc2].
      remember (max i1 i2) as i_max.
      apply (ceval_step_more i1 i_max _ _ _) in IHc1; try lia.
      apply (ceval_step_more i2 i_max _ _ _) in IHc2; try lia.
      eexists.
      apply while_middle_state_exists; try assumption.
      eexists.
      split.
      -- apply IHc1.
      -- apply IHc2.
Qed.

(**
    This proves the equivalence between the evaluators, relying on ceval_step__ceval and ceval__ceval_step)
 *)
Theorem ceval_and_ceval_step_coincide: forall c st st',
      st =[ c ]=> st'
  <-> exists i, In (Some st') (ceval_step st c i).
Proof.
  intros.
  split.
  - apply ceval__ceval_step.
  - apply ceval_step__ceval.
Qed.
