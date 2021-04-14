From Coq Require Import Lia.
From Coq Require Import Arith.Arith.
From FirstProject Require Import Imp Maps.


(* 3.1. TODO: Change/extend ceval_step as specified *)

Notation "'LETOPT' x <== e1 'IN' e2"
   := (match e1 with
         | Some x => e2
         | None => None
       end)
   (right associativity, at level 60).

Fixpoint ceval_step (st : state) (c : com) (i : nat)
                    : option state :=
  match i with
  | O => None
  | S i' =>
    match c with
      | <{ skip }> =>
          Some st
      | <{ l := a1 }> =>
          Some (l !-> aeval st a1 ; st)
      | <{ c1 ; c2 }> =>
          LETOPT st' <== ceval_step st c1 i' IN
          ceval_step st' c2 i'
      | <{ if b then c1 else c2 end }> =>
          if (beval st b)
            then ceval_step st c1 i'
            else ceval_step st c2 i'
      | <{ while b1 do c1 end }> =>
          if (beval st b1)
          then LETOPT st' <== ceval_step st c1 i' IN
               ceval_step st' c i'
          else Some st
    end
  end.

Definition test_ceval (st:state) (c:com) :=
  match ceval_step st c 500 with
  | None    => None
  | Some st => Some (st X, st Y, st Z)
  end.

(* Compute
     (test_ceval empty_st
         (X ::= 2;;
          TEST (X <= 1)
            THEN Y ::= 3
            ELSE Z ::= 4
          FI)).
   ====>
      Some (2, 0, 4)   *)


(* ################################################################# *)
(** * Relational vs. Step-Indexed Evaluation *)

(* 3.2. TODO: Prove ceval_step__ceval, ceval_step_more, 
	ceval__ceval_step, and ceval_and_ceval_step_coincide 
	(for the new implementation of the step-indexed evaluator) *)


Theorem ceval_step__ceval: forall c st st',
      (exists i, In (Some st') (ceval_step st c i)) ->
      st =[ c ]=> st'.
Proof.
Admitted.

Theorem ceval_step_more: forall i1 i2 st st' c,
  i1 <= i2 ->
  In (Some st') (ceval_step st c i1) ->
  In (Some st') (ceval_step st c i2).
Proof.
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
