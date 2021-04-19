From Coq Require Import Lia.
From Coq Require Import Lists.List.
From Coq Require Import Arith.Arith.
From FirstProject Require Import Imp Maps.
Import ListNotations.

(* 3.1. TODO: Change/extend ceval_step as specified *)

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

Lemma opt_eq: forall T (a b: T), (Some a) = (Some b) <-> a = b.
Proof.
  intros.
  split; inversion 1; reflexivity.
Qed.

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
       destruct H; try contradiction; simpl.
       rewrite opt_eq in H.
       rewrite H.
       apply E_Skip.
    -- (* := *)
       destruct H. rewrite opt_eq in H. incersion 1.


Admitted.

Theorem ceval_step_more: forall i1 i2 st st' c,
  i1 <= i2 ->
  In (Some st') (ceval_step st c i1) ->
  In (Some st') (ceval_step st c i2).
Proof.
  intros.
Admitted.

(* ceval_step_more can be used in the proof of ceval__ceval_step *)
Theorem ceval__ceval_step: forall c st st',
      st =[ c ]=> st' ->
      exists i, In (Some st') (ceval_step st c i).
Proof.
Admitted.

Theorem ceval_and_ceval_step_coincide: forall c st st',
      st =[ c ]=> st'
  <-> exists i, In (Some st') (ceval_step st c i).
Proof.
Admitted.
