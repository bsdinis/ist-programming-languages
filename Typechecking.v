(** * Typechecking: A Typechecker for STLC *)
Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From SecondProject Require Import Maps.
From SecondProject Require Import Smallstep.
From SecondProject Require Import Stlc.
From SecondProject Require MoreStlc.

(* ################################################################# *)
(** * The Typechecker *)

(** The typechecker works by walking over the structure of the given
    term, returning either [Some T] or [None].  Each time we make a
    recursive call to find out the types of the subterms, we need to
    pattern-match on the results to make sure that they are not
    [None].  Also, in the [app] case, we use pattern matching to
    extract the left- and right-hand sides of the function's arrow
    type (and fail if the type of the function is not [T11->T12]
    for some [T11] and [T12]). *)

(** Before we consider the properties of this algorithm, let's write
    it out again in a cleaner way, using "monadic" notations in the
    style of Haskell to streamline the plumbing of options.  First, we
    define a notation for composing two potentially failing (i.e.,
    option-returning) computations: *)

Notation " x <- e1 ;; e2" := (match e1 with
                              | Some x => e2
                              | None => None
                              end)
         (right associativity, at level 60).

(** Second, we define [return] and [fail] as synonyms for [Some] and
    [None]: *)

Notation " 'return' e "
  := (Some e) (at level 60).

Notation " 'fail' "
  := None.


(* ################################################################# *)
(** **** Exercise: 5 stars, standard (typechecker_extensions)

    In this exercise we'll extend the typechecker to deal with the
    extended features discussed in chapter [MoreStlc].  Your job
    is to fill in the omitted cases in the following. *)

Module TypecheckerExtensions.
(* Do not modify the following line: *)
Definition manual_grade_for_type_checking_sound : option (nat*string) := None.
(* Do not modify the following line: *)
Definition manual_grade_for_type_checking_complete : option (nat*string) := None.
Import MoreStlc.
Import STLCExtended.

Fixpoint eqb_ty (T1 T2 : ty) : bool :=
  match T1,T2 with
  | <{{Nat}}>, <{{Nat}}> =>
      true
  | <{{Unit}}>, <{{Unit}}> =>
      true
  | <{{T11 -> T12}}>, <{{T21 -> T22}}> =>
      andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | <{{T11 * T12}}>, <{{T21 * T22}}> =>
      andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | <{{T11 + T12}}>, <{{T21 + T22}}> =>
      andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | <{{List T11}}>, <{{List T21}}> =>
      eqb_ty T11 T21
  | <{{T11 !! T12}}>, <{{T21 !! T22}}> =>
      andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | _,_ =>
      false
  end.

Lemma eqb_ty_refl : forall T,
  eqb_ty T T = true.
Proof.
  intros T.
  induction T; simpl; auto;
    rewrite IHT1; rewrite IHT2; reflexivity.  Qed.

Lemma eqb_ty__eq : forall T1 T2,
  eqb_ty T1 T2 = true -> T1 = T2.
Proof.
  intros T1.
  induction T1; intros T2 Hbeq; destruct T2; inversion Hbeq;
    try reflexivity;
    try (rewrite andb_true_iff in H0; inversion H0 as [Hbeq1 Hbeq2];
         apply IHT1_1 in Hbeq1; apply IHT1_2 in Hbeq2; subst; auto);
    try (apply IHT1 in Hbeq; subst; auto).
Qed.

Fixpoint type_check (Gamma : context) (t : tm) : option ty :=
  match t with
  | tm_var x =>
      match Gamma x with
      | Some T => return T
      | None   => fail
      end
  | <{ \ x1 : T1, t2 }> =>
      T2 <- type_check (x1 |-> T1 ; Gamma) t2 ;;
      return <{{T1 -> T2}}>
  | <{ t1 t2 }> =>
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match T1 with
      | <{{T11 -> T12}}> =>
          if eqb_ty T11 T2 then return T12 else fail
      | _ => fail
      end
  | tm_const _ =>
      return <{{Nat}}>
  | <{ succ t1 }> =>
      T1 <- type_check Gamma t1 ;;
      match T1 with
      | <{{Nat}}> => return <{{Nat}}>
      | _ => fail
      end
  | <{ pred t1 }> =>
      T1 <- type_check Gamma t1 ;;
      match T1 with
      | <{{Nat}}> => return <{{Nat}}>
      | _ => fail
      end
  | <{ t1 * t2 }> =>
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match T1, T2 with
      | <{{Nat}}>, <{{Nat}}> => return <{{Nat}}>
      | _,_        => fail
      end
  | <{ if0 guard then t else f }> =>
      Tguard <- type_check Gamma guard ;;
      T1 <- type_check Gamma t ;;
      T2 <- type_check Gamma f ;;
      match Tguard with
      | <{{Nat}}> => if eqb_ty T1 T2 then return T1 else fail
      | _ => fail
      end

  (* sums *)
  | <{ inl TR t }> =>
      T <- type_check Gamma t ;;
      return <{{ T + TR }}>
  | <{ inr TL t }> =>
      T <- type_check Gamma t ;;
      return <{{ TL + T }}>
  | <{case t0 of | inl x1 => t1 | inr x2 => t2}> =>
      T0 <- type_check Gamma t0 ;;
      match T0 with
      | <{{ X1 + X2 }}> =>
        T1 <- type_check (x1 |-> X1; Gamma) t1 ;;
        T2 <- type_check (x2 |-> X2; Gamma) t2 ;;
        if eqb_ty T1 T2 then return T1 else fail
      | _ => fail
      end

  (* lists (the [tlcase] is given for free) *)
  | <{ nil T }> => return <{{ List T }}>
  | <{ h :: t }> =>
    TH <- type_check Gamma h ;;
    TT <- type_check Gamma t ;;
    match TT with
    | <{{ List T }}> => if eqb_ty T TH then return TT else fail
    | _ => fail
    end
  | <{ case t0 of | nil => t1 | x21 :: x22 => t2 }> =>
      T0 <- type_check Gamma t0 ;;
      match T0 with
      | <{{ List T }}> =>
        T1 <- type_check Gamma t1 ;;
        T2 <- type_check (x21 |-> T ; x22 |-> <{{List T}}> ; Gamma) t2 ;;
        if eqb_ty T1 T2 then return T1 else fail
      | _ => fail
      end

  (* unit *)
  | <{ unit }> => return <{{ Unit }}>
  (* pairs *)
  | <{ (t1, t2) }> =>
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      return <{{ T1 * T2 }}>
  | <{ t.fst }> =>
      T <- type_check Gamma t ;;
      match T with
      | <{{ T1 * _ }}> => return T1
      | _ => fail
      end
  | <{ t.snd }> =>
      T <- type_check Gamma t ;;
      match T with
      | <{{ _ * T2 }}> => return T2
      | _ => fail
      end
  (* let *)
  | <{ let x = t1 in t2 }> =>
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check ( x |-> T1 ; Gamma) t2 ;;
      return T2
  (* fix *)
  | <{ fix t }> =>
      T <- type_check Gamma t ;;
      match T with
      | <{{ TT1 -> TT2 }}> => if eqb_ty TT1 TT2 then return TT1 else fail
      | _ => fail
      end
  (* non-deterministic choice *)
  | <{ t1 !! t2 }> =>
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      if eqb_ty T1 T2 then return T1 else fail
  end.

Example type_sum_inl: type_check empty <{ inl (List Nat) 0 }> = Some <{{ Nat + (List Nat) }}>.
Proof. auto. Qed.

Example type_sum_inr: type_check empty <{ inr Nat (0 :: nil Nat) }> = Some <{{ Nat + (List Nat) }}>.
Proof. auto. Qed.

(* If the branches do not match, do not type check *)
Example type_sum_case_neg: type_check empty <{
  case (inr Nat (0 :: nil Nat)) of
    | inl x => 0
    | inr y => nil Nat }> = None.
Proof. auto. Qed.

(* If the branches do match, do type check *)
Example type_sum_case_pos: type_check empty <{
  case (inr Nat (0 :: nil Nat)) of
    | inl x => 0
    | inr y => 0 }> = Some <{{ Nat }}>.
Proof. auto. Qed.

Example type_list_nil: type_check empty <{ nil Nat }> = Some <{{ List Nat }}>.
Proof. auto. Qed.

Example type_list_cons: type_check empty <{ 0 :: nil Nat}> = Some <{{ List Nat }}>.
Proof. auto. Qed.

Example type_unit: type_check empty <{ unit }> = Some <{{ Unit }}>.
Proof. auto. Qed.

Example type_pair: type_check empty <{ (0, nil (List Nat)) }> = Some <{{ Nat * (List (List Nat)) }}>.
Proof. auto. Qed.

Example type_pair_fst: type_check empty <{ (0, nil (List Nat)).fst }> = Some <{{ Nat  }}>.
Proof. auto. Qed.

Example type_pair_snd: type_check empty <{ (0, nil (List Nat)).snd }> = Some <{{ (List (List Nat)) }}>.
Proof. auto. Qed.

Example type_let: type_check empty <{ let x = 3 in <{ x * 4 }> }> = Some <{{ Nat }}>.
Proof. auto. Qed.

Open Scope string_scope.
Notation x := "x".
Notation y := "y".
Notation a := "a".
Notation f := "f".
Definition fact :=
  <{fix
      (\f:Nat->Nat,
        \a:Nat,
         if0 a then 1 else (a * (f (pred a))))}>.

Example type_fix: type_check empty <{ fact }> = Some <{{ Nat -> Nat }}>.
Proof. auto. Qed.

(* If the branches do not match, do not type check *)
Example type_non_det_neg: type_check empty <{ 0 !! nil Nat }> = None.
Proof. auto. Qed.

(* If the branches do match, do type check *)
Example type_non_det_pos: type_check empty <{ 0 !! 1 }> = Some <{{ Nat }}>.
Proof. auto. Qed.

(** Just for fun, we'll do the soundness proof with just a bit more
    automation than above, using these "mega-tactics": *)

Ltac invert_typecheck Gamma t T :=
  remember (type_check Gamma t) as TO;
  destruct TO as [T|];
  try solve_by_invert; try (inversion H0; eauto); try (subst; eauto).

Ltac analyze T T1 T2 :=
  destruct T as [T1 T2| |T1 T2| T1 | |T1 T2 | T1 T2]; try solve_by_invert.

Ltac fully_invert_typecheck Gamma t T T1 T2 :=
  let TX := fresh T in
  remember (type_check Gamma t) as TO;
  destruct TO as [TX|]; try solve_by_invert;
  destruct TX as [T1 T2| |T1 T2|T1| |T1 T2 | T1 T2];
  try solve_by_invert; try (inversion H0; eauto); try (subst; eauto).

Ltac case_equality S T :=
  destruct (eqb_ty S T) eqn: Heqb;
  inversion H0; apply eqb_ty__eq in Heqb; subst; subst; eauto.

Theorem type_checking_sound : forall Gamma t T,
  type_check Gamma t = Some T ->
  has_type Gamma t T.
Proof with eauto.
  intros Gamma t. generalize dependent Gamma.
  induction t; intros Gamma T Htc; inversion Htc.
  - (* var *) rename s into x. destruct (Gamma x) eqn:H.
    rename t into T'. inversion H0. subst. eauto. solve_by_invert.
  - (* app *)
    invert_typecheck Gamma t1 T1.
    invert_typecheck Gamma t2 T2.
    analyze T1 T11 T12.
    case_equality T11 T2.
  - (* abs *)
    rename s into x, t into T1.
    remember (x |-> T1 ; Gamma) as Gamma'.
    invert_typecheck Gamma' t0 T0.
  - (* const *) eauto.
  - (* scc *)
    rename t into t1.
    fully_invert_typecheck Gamma t1 T1 T11 T12.
  - (* prd *)
    rename t into t1.
    fully_invert_typecheck Gamma t1 T1 T11 T12.
  - (* mlt *)
    invert_typecheck Gamma t1 T1.
    invert_typecheck Gamma t2 T2.
    analyze T1 T11 T12; analyze T2 T21 T22.
    inversion H0. subst. eauto.
  - (* test0 *)
    invert_typecheck Gamma t1 T1.
    invert_typecheck Gamma t2 T2.
    invert_typecheck Gamma t3 T3.
    destruct T1; try solve_by_invert.
    case_equality T2 T3.
  - (* inl *)
    rename t into TR, t0 into t.
    fully_invert_typecheck Gamma t T1 T11 T12.
  - (* inr *)
    rename t into TL, t0 into t.
    fully_invert_typecheck Gamma t T1 T11 T12.
  - (* case *)
    rename s into x1, s0 into x2.
    rename t1 into t0, t2 into t1, t3 into t2.
    fully_invert_typecheck Gamma t0 T0 T01 T02.
    invert_typecheck (x1 |-> T01; Gamma) t1 T1.
    invert_typecheck (x2 |-> T02; Gamma) t2 T2.
    case_equality T1 T2.
  - (* nil *)
    rename T into LT, t into T.
    invert_typecheck Gamma <{ nil T }> T'.
  - (* t1 :: t2 *)
    admit.
  - (* tlcase *)
    rename s into x31, s0 into x32.
    fully_invert_typecheck Gamma t1 T1 T11 T12.
    invert_typecheck Gamma t2 T2.
    remember (x31 |-> T11 ; x32 |-> <{{List T11}}> ; Gamma) as Gamma'2.
    invert_typecheck Gamma'2 t3 T3.
    case_equality T2 T3.
  - (* unit *)
    fully_invert_typecheck Gamma <{ unit }> T T1 T2.
  - (* pair *)
    invert_typecheck Gamma t1 T1.
    invert_typecheck Gamma t2 T2.
  - (* fst *)
    fully_invert_typecheck Gamma t TP T11 T12.
  - (* snd *)
    fully_invert_typecheck Gamma t TP T11 T12.
  - (* let *)
    invert_typecheck Gamma t1 T1.
    invert_typecheck ( s |-> T1; Gamma) t2 T2.
  - (* fix *)
    fully_invert_typecheck Gamma t TF T11 T12.
    case_equality T11 T12.
  - (* non det *)
    invert_typecheck Gamma t1 T1.
    invert_typecheck Gamma t2 T2.
    case_equality T1 T2.
Admitted.

Theorem type_checking_complete : forall Gamma t T,
  has_type Gamma t T ->
  type_check Gamma t = Some T.
Proof.
  intros Gamma t T Hty.
  induction Hty; simpl;
    try (rewrite IHHty);
    try (rewrite IHHty1);
    try (rewrite IHHty2);
    try (rewrite IHHty3);
    try (rewrite (eqb_ty_refl T0));
    try (rewrite (eqb_ty_refl T1));
    try (rewrite (eqb_ty_refl T2));
    try (rewrite (eqb_ty_refl T3));
    eauto.
    - destruct (Gamma x0); [assumption| solve_by_invert].
Admitted.
End TypecheckerExtensions.


(* TODO *)
(** **** Exercise: 5 stars, standard, optional (stlc_step_function)

    Above, we showed how to write a typechecking function and prove it
    sound and complete for the typing relation.  Do the same for the
    operational semantics -- i.e., write a _function_ [stepf] of type
    [tm -> option tm] and prove that it is sound and complete with
    respect to [step] from chapter [MoreStlc]. *)

Module StepFunction.
Import MoreStlc.
Import STLCExtended.

(* Operational semantics as a Coq function. *)
Fixpoint stepf (t : tm) : option tm :=
  match t with
  | <{ fix t' }> => Some t'
  | _ => None
  end.

  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

  (* TODO *)
(* Soundness of [stepf]. *)
Theorem sound_stepf : forall t t',
    stepf t = Some t'  ->  t --> t'.
Proof. (* TODO *) Admitted.

(* TODO *)
(* Completeness of [stepf]. *)
Theorem complete_stepf : forall t t',
    t --> t'  ->  stepf t = Some t'.
Proof. (* TODO *) Admitted.

End StepFunction.
(** [] *)

(** **** Exercise: 5 stars, standard, optional (stlc_impl)

    Using the Imp parser described in the [ImpParser] chapter
    of _Logical Foundations_ as a guide, build a parser for extended
    STLC programs.  Combine it with the typechecking and stepping
    functions from the above exercises to yield a complete typechecker
    and interpreter for this language. *)

Module StlcImpl.
Import StepFunction.

(* EXTRA *)
End StlcImpl.


