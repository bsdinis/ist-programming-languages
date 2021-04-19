(** * Imp: Simple Imperative Programs *)

(** Taken from the chapter Imp:
  https://softwarefoundations.cis.upenn.edu/lf-current/Imp.html

    It might be a good idea to read the chapter before or as you
    develop your solution.
*)

Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lia.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
Import ListNotations.

From FirstProject Require Import Maps.

(* Note that we follow the same convention as in the Imp chapter:
   our states are total maps
*)
Definition state := total_map nat.

(* ================================================================= *)
(** ** Syntax  *)

Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

(* ================================================================= *)
(** ** Notations *)

(** To make Imp programs easier to read and write, we use the same notation
as used in the book *)

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.

Declare Custom Entry com.
Declare Scope com_scope.
Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.
Notation "x + y" := (APlus x y) (in custom com at level 50, left associativity).
Notation "x - y" := (AMinus x y) (in custom com at level 50, left associativity).
Notation "x * y" := (AMult x y) (in custom com at level 40, left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := BTrue (in custom com at level 0).
Notation "'false'"  := false (at level 1).
Notation "'false'"  := BFalse (in custom com at level 0).
Notation "x <= y" := (BLe x y) (in custom com at level 70, no associativity).
Notation "x = y"  := (BEq x y) (in custom com at level 70, no associativity).
Notation "x && y" := (BAnd x y) (in custom com at level 80, left associativity).
Notation "'~' b"  := (BNot b) (in custom com at level 75, right associativity).

Open Scope com_scope.

(** We can now write [3 + (X * 2)] instead  of [APlus 3 (AMult X 2)],
    and [true && ~(X <= 4)] instead of [BAnd true (BNot (BLe X 4))]. *)

Definition example_aexp : aexp := <{ 3 + (X * 2) }>.
Definition example_bexp : bexp := <{ true && ~(X <= 4) }>.

(* ================================================================= *)
(** ** Evaluation *)

(** The arith and boolean evaluators are extended to handle
    variables in the obvious way, taking a state as an extra
    argument: *)

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x
  | <{a1 + a2}> => (aeval st a1) + (aeval st a2)
  | <{a1 - a2}> => (aeval st a1) - (aeval st a2)
  | <{a1 * a2}> => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | <{true}>      => true
  | <{false}>     => false
  | <{a1 = a2}>   => (aeval st a1) =? (aeval st a2)
  | <{a1 <= a2}>  => (aeval st a1) <=? (aeval st a2)
  | <{~ b1}>      => negb (beval st b1)
  | <{b1 && b2}>  => andb (beval st b1) (beval st b2)
  end.

(** We specialize our notation for total maps to the specific case of
    states, i.e. using [(_ !-> 0)] as empty state. *)

Definition empty_st := (_ !-> 0).

(** Now we can add a notation for a "singleton state" with just one
    variable bound to a value. *)
Notation "x '!->' v" := (t_update empty_st x v) (at level 100).

Example aexp1 :
    aeval (X !-> 5) <{ (3 + (X * 2))}>
  = 13.
Proof. reflexivity. Qed.

Example bexp1 :
    beval (X !-> 5) <{ true && ~(X <= 4)}>
  = true.
Proof. reflexivity. Qed.

(* ################################################################# *)
(** * Commands *)

(** Now we are ready define the syntax and behavior of Imp
    _commands_ (sometimes called _statements_). *)

(* ================================================================= *)
(** ** Syntax *)

(** Informally, commands [c] are described by the following BNF
    grammar.

     c := skip | x := a | c ; c | if b then c else c end
         | while b do c end
*)

(** Here is the formal definition of the abstract syntax of
    commands: *)

(* 1.1. DONE: Extend the datatype com with a new construct for non-deterministic choice. *)
Inductive com : Type :=
  | CSkip
  | CAss (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CNonDet (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

(** As for expressions, we can use a few [Notation] declarations to
    make reading and writing Imp programs more convenient. *)

(* 1.2. DONE: Define a new notation for the new construct. *)
Notation "'skip'"  :=
         CSkip (in custom com at level 0) : com_scope.
Notation "x := y"  :=
         (CAss x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity) : com_scope.
Notation "x !! y" :=
         (CNonDet x y)
           (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99) : com_scope.

(** For example, here is the factorial function again, written as a
    formal definition to Coq: *)

Definition fact_in_coq : com :=
  <{ Z := X;
     Y := 1;
     while ~(Z = 0) do
       Y := Y * Z;
       Z := Z - 1
     end }>.

(* ================================================================= *)
(** ** Evaluation as a Relation *)

(** We'll use the notation [st =[ c ]=> st'] for the [ceval] relation:
    [st =[ c ]=> st'] means that executing program [c] in a starting
    state [st] results in an ending state [st'].  This can be
    pronounced "[c] takes state [st] to [st']". *)

(* ----------------------------------------------------------------- *)
(** *** Operational Semantics *)

(** Here is an informal definition of evaluation, presented as inference
    rules for readability:

                           -----------------                            (E_Skip)
                           st =[ skip ]=> st

                           aeval st a = n
                   -------------------------------                      (E_Ass)
                   st =[ x := a ]=> (x !-> n ; st)

                           st  =[ c1 ]=> st'
                           st' =[ c2 ]=> st''
                         ---------------------                           (E_Seq)
                         st =[ c1;c2 ]=> st''

                          beval st b = true
                           st =[ c1 ]=> st'
                --------------------------------------               (E_IfTrue)
                st =[ if b then c1 else c2 end ]=> st'

                         beval st b = false
                           st =[ c2 ]=> st'
                --------------------------------------              (E_IfFalse)
                st =[ if b then c1 else c2 end ]=> st'

                         beval st b = false
                    -----------------------------                 (E_WhileFalse)
                    st =[ while b do c end ]=> st

                          beval st b = true
                           st =[ c ]=> st'
                  st' =[ while b do c end ]=> st''
                  --------------------------------                 (E_WhileTrue)
                  st  =[ while b do c end ]=> st''
*)

(** Here is the formal definition.  Make sure you understand
    how it corresponds to the inference rules. *)

Reserved Notation
         "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).

(* 1.3. DONE: Extend the relational semantics (ceval) to support non-deterministic choice. *)

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Ass  : forall st a n x,
      aeval st a = n ->
      st =[ x := a ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ; c2 ]=> st''
  | E_NonDet : forall c1 c2 st st',
      (st  =[ c1 ]=> st') \/ (st  =[ c2 ]=> st')  ->
      st  =[ c1 !! c2 ]=> st'
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st  =[ while b do c end ]=> st''

  where "st =[ c ]=> st'" := (ceval c st st').

(** The cost of defining evaluation as a relation instead of a
    function is that we now need to construct _proofs_ that some
    program evaluates to some result state, rather than just letting
    Coq's computation mechanism do it for us. *)

Example ceval_example1:
  empty_st =[
     X := 2;
     if (X <= 1)
       then Y := 3
       else Z := 4
     end
  ]=> (Z !-> 4 ; X !-> 2).
Proof.
  (* We must supply the intermediate state *)
  apply E_Seq with (X !-> 2).
  - (* assignment command *)
    apply E_Ass. reflexivity.
  - (* if command *)
    apply E_IfFalse.
    reflexivity.
    apply E_Ass. reflexivity.
Qed.

(* 1.4. DONE: Use the new relational semantics to prove the examples
ceval_example_choice1, ceval_example_choice2, and ceval_example_choice3

   @bsd: you guys should re-do these proofs
*)

Example ceval_example_choice1:
  empty_st =[
    X := 0 ; (Y := 1 !! Z := 2)
  ]=> (Z !-> 2 ; X !-> 0).
Proof.
  apply E_Seq with (X !-> 0).
  - (* assignment *)
    apply E_Ass. reflexivity.
  - (* non deterministic *)
    apply E_NonDet.
    right.
    apply E_Ass. reflexivity.
Qed.

Example ceval_example_choice2:
  empty_st =[
    X := 0 ; (Y := 1 !! Z := 2)
  ]=> (Y !-> 1 ; X !-> 0).
Proof.
  apply E_Seq with (X !-> 0).
  - (* assignment *)
    apply E_Ass. reflexivity.
  - (* non deterministic *)
    apply E_NonDet.
    left.
    apply E_Ass. reflexivity.
Qed.


Example ceval_example_choice3:
  (X !-> 4) =[
    <{ while ~(X = 0) do
          (X := X - 1) !! (X := X + 1)
     end }>
  ]=> (X !-> 0).
Proof.
  apply E_WhileTrue with (X !-> 3; X !-> 4); simpl; try reflexivity.
  - (* first iteration *)
    apply E_NonDet.
    left.
    apply E_Ass. reflexivity.
  - (* tail *)
    apply E_WhileTrue with (X !-> 2; X !-> 3; X !-> 4); simpl; try reflexivity.
    -- (* second iteration *)
      apply E_NonDet.
      left.
      apply E_Ass. reflexivity.
    -- apply E_WhileTrue with (X !-> 1; X !-> 2; X !-> 3; X !-> 4); simpl; try reflexivity.
       --- (* third iteration *)
        apply E_NonDet.
        left.
        apply E_Ass. reflexivity.
       --- apply E_WhileTrue with (X !-> 0; X !-> 1; X !-> 2; X !-> 3; X !-> 4); simpl; try reflexivity.
           ---- (* fourth iteration *)
            apply E_NonDet.
            left.
            apply E_Ass. reflexivity.
           ----
                repeat rewrite t_update_shadow.
                apply E_WhileFalse.
                simpl.
                reflexivity.
Qed.


(* ================================================================= *)
(** ** Behavioral equivalence and algebraic properties *)

Definition cequiv (c1 c2 : com) : Prop := forall (st st' : state),
    (st =[ c1 ]=> st') <-> (st =[ c2 ]=> st').

Infix "==" := cequiv (at level 99).

(* 2. DONE: Prove the following properties of non-deterministic choice *)

(* When both branches are the same, the non-deterministic choice is deterministic
   Probability parallel:
        if both sides of a coin are the same,
        flipping the coin is deterministic
 *)
Lemma choice_idempotent: forall c,
  <{ c !! c }> == <{ c }>.
Proof.
 intros c.
  split.
  - (* -> *)
    intros H.
    inversion H; subst.
    destruct H4; assumption.
  - (* <- *)
    intros H.
    apply E_NonDet.
    left. (* or right *)
    assumption.
Qed.

(* The order in which programs appear in the non-deterministic choice
    is irrelevant.
 *)
Lemma choice_comm: forall c1 c2,
  <{ c1 !! c2 }> == <{ c2 !! c1 }>.
Proof.
  intros c1 c2.
  split;
  intros H;
  inversion H as [ | | | c1' c2' a_st a_st' H_dis H1 H2 H3 | | | | ];
      subst;
      destruct H_dis;
      apply E_NonDet;
      try (left; assumption); try (right; assumption).
Qed.

(* The choice is also associative.
   This means that we can all choices from  N programs are the same,
   no matter the grouping.
 *)
Lemma choice_assoc: forall c1 c2 c3,
  <{ (c1 !! c2) !! c3 }> == <{ c1 !! (c2 !! c3) }>.
Proof.
  intros c1 c2 c3.
  split.
  - (* -> *)
    intros H.
    inversion H as [ | | | c1' c2' a_st a_st' H_dis H1 H2 H3 | | | | ];
    subst.
    destruct H_dis as [H12 | H3];  apply E_NonDet.
    -- inversion H12 as [ | | | c1' c2' a_st a_st' H_dis' H1 H2 H3 | | | | ]. subst.
       destruct H_dis' as [H1 | H2].
       --- left; assumption.
       --- right. apply E_NonDet. left. assumption.
    -- right. apply E_NonDet. right. assumption.
  - (* <- *)
    intros H.
    inversion H as [ | | | c1' c2' a_st a_st' H_dis H1 H2 H3 | | | | ];
    subst.
    destruct H_dis as [H1 | H23];  apply E_NonDet.
    -- left. apply E_NonDet. left. assumption.
    -- inversion H23 as [ | | | c1' c2' a_st a_st' H_dis' H1 H2 H3 | | | | ]. subst.
       destruct H_dis' as [H2 | H3].
       --- left. apply E_NonDet. right. assumption.
       --- right. assumption.
Qed.

(* Non deterministic choice left distributes sequence
   This means that we can ``factor out'' a left common sequence,
   or distribute a left sequence inside the choice.
*)
Lemma choice_seq_distr_l: forall c1 c2 c3,
  <{ c1 ; (c2 !! c3)}> == <{ (c1;c2) !! (c1;c3) }>.
Proof.
  intros.
  split.
  - (* -> *)
    intros H.
    inversion H as [ | | d1 d2 a_st a_st' a_st'' Hc1 Hc23  | | | | | ]; subst.
    inversion Hc23 as [ | | |  e1 e2 b_st b_st' Hc23_dis |  | | | ]; subst.
    apply E_NonDet.
    destruct Hc23_dis as [Hc2 | Hc3].
    -- left. apply E_Seq with a_st'; assumption.
    -- right. apply E_Seq with a_st'; assumption.
  - (* <- *)
    intros H.
    inversion H as [ | | | d1 d2 a_st a_st' Hdis  | | | | ]; subst.
    destruct Hdis as [ Hc12 | Hc13 ].
    -- inversion Hc12 as [ | | c1' c2' a_st a_st' a_st'' Hc1 Hc2 | | | | |]; subst.
       apply E_Seq with a_st'.
       assumption.
       apply E_NonDet.
       left.
       assumption.
    -- inversion Hc13 as [ | | c1' c2' a_st a_st' a_st'' Hc1 Hc3 | | | | |]; subst.
       apply E_Seq with a_st'.
       assumption.
       apply E_NonDet.
       right.
       assumption.
Qed.

(* Non deterministic choice right distributes sequence
   This means that we can ``factor out'' a right common sequence,
   or distribute a right sequence inside the choice.
*)
Lemma choice_seq_distr_r: forall c1 c2 c3,
  <{ (c1 !! c2) ; c3 }> == <{ (c1;c3) !! (c2;c3) }>.
Proof.
  intros.
  split.
  - (* -> *)
    intros H.
    inversion H as [ | | d1 d2 a_st a_st' a_st'' Hc12 Hc3  | | | | | ]; subst.
    inversion Hc12 as [ | | |  e1 e2 b_st b_st' Hc12_dis |  | | | ]; subst.
    apply E_NonDet.
    destruct Hc12_dis as [Hc1 | Hc2].
    -- left; apply E_Seq with a_st'; assumption.
    -- right; apply E_Seq with a_st'; assumption.
  - (* <- *)
    intros H.
    inversion H as [ | | | d1 d2 a_st a_st' Hdis  | | | | ]; subst.
    destruct Hdis as [ Hc13 | Hc23 ].
    -- inversion Hc13 as [ | | c1' c2' a_st a_st' a_st'' Hc1 Hc3 | | | | |]; subst.
       apply E_Seq with a_st'.
       apply E_NonDet.
       left.
       assumption.
       assumption.
    -- inversion Hc23 as [ | | c1' c2' a_st a_st' a_st'' Hc2 Hc3 | | | | |]; subst.
       apply E_Seq with a_st'.
       apply E_NonDet.
       right.
       assumption.
       assumption.
Qed.

(* If two pairs are equal, their choice is also congruent
 *)
Lemma choice_congruence: forall c1 c1' c2 c2',
  c1 == c1' -> c2 == c2' ->
  <{ c1 !! c2 }> == <{ c1' !! c2' }>.
Proof.
  intros c1 c1' c2 c2' H1 H2.
  split.
  - (* -> *)
    intros H.
    inversion H as [ | | | d1 d2 a_st a_st' H_dis H1' H2' H3' | | | | ]; subst.
    destruct H_dis as [ Hc1 | Hc2 ]; apply E_NonDet.
    -- left. apply H1 in Hc1. assumption.
    -- right. apply H2 in Hc2. assumption.
  - (* <- *)
    intros H.
    inversion H as [ | | | d1 d2 a_st a_st' H_dis H1' H2' H3' | | | | ]; subst.
    destruct H_dis as [ Hc1' | Hc2' ]; apply E_NonDet.
    -- left. apply H1 in Hc1'. assumption.
    -- right. apply H2 in Hc2'. assumption.
Qed.
