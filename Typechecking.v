(** * Typechecking: A Typechecker for STLC *)
Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From SecondProject Require Import Maps.
From SecondProject Require Import Smallstep.
From SecondProject Require Import Stlc.
From SecondProject Require MoreStlc.
Require Import Coq.Lists.List.
Import ListNotations.

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
    invert_typecheck Gamma t1 T1.
    fully_invert_typecheck Gamma t2 T2 T21 T22.
    rename T21 into T2.
    destruct eqb_ty eqn:Heq; try solve_by_invert.
    apply eqb_ty__eq in Heq.
    subst.
    invert_typecheck Gamma <{ t1 :: t2 }> T'.
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
Qed.

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
    try (rewrite (eqb_ty_refl T));
    try (rewrite (eqb_ty_refl T0));
    try (rewrite (eqb_ty_refl T1));
    try (rewrite (eqb_ty_refl T2));
    try (rewrite (eqb_ty_refl T3));
    eauto.
    - destruct (Gamma x); [assumption| solve_by_invert].
Qed.
End TypecheckerExtensions.


(** **** Exercise: 5 stars, standard, optional (stlc_step_function)

    Above, we showed how to write a typechecking function and prove it
    sound and complete for the typing relation.  Do the same for the
    operational semantics -- i.e., write a _function_ [stepf] of type
    [tm -> option tm] and prove that it is sound and complete with
    respect to [step] from chapter [MoreStlc]. *)

Module StepFunction.
Import MoreStlc.
Import STLCExtended.

Fixpoint is_value (t: tm) : bool :=
  match t with
  | <{\x:T2, t1}> => true
  | tm_const _ => true
  | <{inl T1 v}> | <{inr T1 v}> => is_value v
  | <{nil _}> => true
  | <{v1 :: v2}> | <{(v1, v2)}> => andb (is_value v1) (is_value v2)
  | <{unit}> => true
  | _ => false
  end.

Lemma is_value__value: forall t,
  is_value t = true -> value t.
Proof.
  intro t.
  intro H.
  induction t; try solve_by_invert.
  - apply v_abs.
  - apply v_nat.
  - apply v_inl. inversion H. auto.
  - apply v_inr. inversion H. auto.
  - apply v_lnil.
  - apply v_lcons; inversion H; apply andb_true_iff in H1; destruct H1 as [H1 H2]; auto.
  - apply v_unit.
  - apply v_pair; inversion H; apply andb_true_iff in H1; destruct H1 as [H1 H2]; auto.
Qed.

Lemma value__is_value: forall t,
  value t -> is_value t = true.
Proof.
Admitted.

(* Operational semantics as a Coq function. *)
Fixpoint stepf (t : tm) : list tm :=
  match t with
  (* pure STLC *)
  | tm_var y => []
  | <{\y:T, t1}> => []
  | <{(\x:T2, t1) v2}> =>
      if is_value v2
        then [ <{ [x:=v2]t1 }> ]
        else map (fun t2' => <{(\x:T2, t1) t2'}>) (stepf v2)
  | <{t1 t2}> =>
      if is_value t1
        then ( if is_value t2
            then []
            else map (fun t2' => <{t1 t2'}>) (stepf t2)
        ) else map (fun t1' => <{t1' t2}>) (stepf t1)

  (* numbers *)
  | tm_const _ => []
  | <{ succ t1 }> =>
      match t1 with
      | tm_const n => [tm_const (S n)]
      | _ => map (fun t1' => <{succ t1'}>) (stepf t1)
      end
  | <{ pred t1 }> =>
      match t1 with
      | tm_const n => [tm_const (n-1)]
      | _ => map (fun t1' => <{pred t1'}>) (stepf t1)
      end
  | <{ t1 * t2 }> =>
      match t1, t2 with
      | tm_const n1, tm_const n2 => [tm_const (n1 * n2)]
      | _, _ => if is_value t1
          then ( if is_value t2
              then []
              else map (fun t2' => <{ t1 * t2' }> ) (stepf t2)

          ) else map (fun t1' => <{ t1' * t2 }> ) (stepf t1)
      end
  | <{if0 t1 then t2 else t3}> =>
      if is_value t1
        then match t1 with
            | tm_const 0 => [t2]
            | tm_const _ => [t3]
            | _ => []
            end
        else map (fun t1' => <{if0 t1' then t2 else t3}> ) (stepf t1)

  (* sums *)
  | <{inl T2 t1}> => map (fun x => <{inl T2 x}>) (stepf t1)
  | <{inr T1 t2}> => map (fun x => <{inr T1 x}>) (stepf t2)
  | <{case t0 of | inl x1 => t1 | inr x2 => t2}> =>
      match t0 with
      | <{ inl T2 v0 }> => if is_value v0
                        then [ <{ [x1:=v0]t1 }> ]
                        else map (fun t0' => <{case t0' of | inl x1 => t1 | inr x2 => t2}> ) (stepf t0)
      | <{ inr T1 v0 }> => if is_value v0
                        then [ <{ [x2:=v0]t2 }> ]
                        else map (fun t0' => <{case t0' of | inl x1 => t1 | inr x2 => t2}> ) (stepf t0)
      | _ => map (fun t0' => <{case t0' of | inl x1 => t1 | inr x2 => t2}> ) (stepf t0)
      end

  (* lists *)
  | <{nil _}> => []
  | <{t1 :: t2}> =>
      if is_value t1
        then ( if is_value t2
            then []
            else map (fun t2' => <{t1 :: t2'}> ) (stepf t2)
        ) else map (fun t1' => <{t1' :: t2}> ) (stepf t1)
  | <{case t1 of | nil => t2 | x1 :: x2 => t3}> =>
      match t1 with
      | <{ nil _ }> => [t2]
      | <{ v1 :: vl }> => if andb (is_value v1) (is_value vl)
                      then [ <{ [x2 := vl] ([x1 := v1] t3) }> ]
                      else  map (fun t1' => <{case t1' of | nil => t2 | x1 :: x2 => t3}> ) (stepf t1)
      | _ => map (fun t1' => <{case t1' of | nil => t2 | x1 :: x2 => t3}> ) (stepf t1)
      end

  (* unit *)
  | <{unit}> => []

  (* pairs *)
  | <{(t1 , t2)}> =>
      if is_value t1
        then ( if is_value t2
            then []
            else map (fun t2' => <{(t1 , t2')}>) (stepf t2)
        ) else map (fun t1' => <{(t1', t2 )}>) (stepf t1)
  | <{t.fst}> =>
      if is_value t
        then match t with
            | <{(v1, _)}> => [v1]
            | _ => []
            end
        else map (fun t' => <{t'.fst}>) (stepf t)
  | <{t.snd}> =>
      if is_value t
        then match t with
            | <{(_, v2)}> => [v2]
            | _ => []
            end
        else map (fun t' => <{t'.snd}>) (stepf t)

  (* let *)
  | <{let x = t1 in t2}> =>
      if is_value t1
        then [ <{ [x:=t1] t2 }> ]
        else map (fun t1' => <{let x = t1' in t2}> ) (stepf t1)

  (* fix *)
  | <{ fix (\xf:T1,t1) }> =>
      [ <{ [xf:=fix (\xf:T1, t1)] t1  }> ]
  | <{ fix t }> =>
      map (fun t' => <{fix t'}>) (stepf t)

  (* non-deterministic choice *)
  | <{t1 !! t2}> => t1 :: [t2]
  end.

(* tactics to solve matching problem when both t1 and t2 are values *)
Ltac solve_app_val12 t1 t2 Hstep Hval1 Hval2 :=
  destruct (is_value t1) eqn:Hval1' in Hstep; try (rewrite Hval1 in Hval1'; inversion Hval1');
  destruct (is_value t2) eqn:Hval2' in Hstep; try (rewrite Hval2 in Hval2'; inversion Hval2');
  inversion Hstep.
Ltac solve_app_val12_pair t1 t2 Hstep Hval1 Hval2 :=
  destruct (is_value t1) eqn:Hval1' in Hstep; try (rewrite Hval1 in Hval1'; inversion Hval1');
  destruct (is_value <{ t1 t2 }>) eqn:Hval12 in Hstep; try (rewrite Hval1 in Hval12; inversion Hval12);
  destruct (is_value t2) eqn:Hval2' in Hstep; try (rewrite Hval2 in Hval2'; inversion Hval2');
  inversion Hstep.

(* tactics to solve matching problem when t1 is a value but t2 is not *)
Ltac solve_app_val1_nval2 t2 Hstep Hval1 Hval2 IHt2:=
  destruct (is_value t2) eqn:Hval2' in Hstep;
  try (rewrite Hval2 in Hval2'; inversion Hval2');
  apply in_map_iff in Hstep;
  destruct Hstep as [x Hstep];
  destruct Hstep as [Ht' Hx];
  rewrite <- Ht';
  apply IHt2 in Hx;
  apply is_value__value in Hval1;
  eauto.

Ltac solve_app_val1_nval2_pair t1 t2 Hstep Hval1 Hval2 IHt1 IHt2:=
        destruct (is_value t2) eqn:Hval2' in Hstep; try (rewrite Hval2 in Hval2'; inversion Hval2');
           destruct (is_value t1 ) eqn:Hval3 in Hstep; try (rewrite Hval2 in Hval3; inversion Hval3);
           apply in_map_iff in Hstep;
           destruct Hstep as [x Hstep];
           destruct Hstep as [Ht' Hx];
           rewrite <- Ht';
           try ( apply IHt2 in Hx; apply is_value__value in Hval1; eauto); try ( apply IHt1 in Hx; apply is_value__value in Hval1; eauto).

(* tactics to solve matching problem when t1 is not a value *)
Ltac solve_app_nval1 t1 Hstep Hval1 IHt1 :=
   destruct (is_value t1 ) eqn:Hval1' in Hstep;
        rewrite Hval1 in Hval1'; inversion Hval1';
        apply in_map_iff in Hstep;
        destruct Hstep as [x Hstep];
        destruct Hstep as [Ht' Hx];
        rewrite <- Ht';
        apply IHt1 in Hx;
        eauto.

Ltac solve_mul_nval t Hstep IHt :=
  destruct (is_value t ) ; try inversion Hstep;
  apply in_map_iff in Hstep;
  destruct Hstep as [x Hstep];
  destruct Hstep as [Ht' Hx];
  try apply IHt in Hx;
  rewrite <- Ht';
  eauto.

Ltac solve_mul_nval_pair t1 t2 Hstep IHt :=
  destruct (is_value t2); try inversion Hstep;
  destruct (is_value t1 ) eqn:Hval1'; try inversion Hstep;
  apply in_map_iff in Hstep;
  destruct Hstep as [x Hstep];
  destruct Hstep as [Ht' Hx];
  try apply IHt in Hx;
  rewrite <- Ht';
  eauto;
  apply is_value__value in Hval1';
  eauto.

Ltac solve_simple t IHt :=
  intros t' Hstep;
  simpl in Hstep;
  destruct (t) ; try solve_by_invert; try (
    apply in_map_iff in Hstep;
    destruct Hstep as [x Hstep];
    destruct Hstep as [Ht' Hx];
    apply IHt in Hx;
    rewrite <- Ht';
    eauto);
  apply in_inv in Hstep;
  destruct Hstep as [H | H];
  try solve_by_invert;
  rewrite <- H;
  eauto.

Theorem sound_stepf : forall t t',
  In t' (stepf t)  ->  t --> t'.
Proof.
  intros t.
  induction t; try (intros t' Hstep; solve_by_invert); try solve_simple t IHt.
  - (* Application *)
    intros t' Hstep.
    destruct (is_value t1) eqn:Hval1.
    + destruct (is_value t2) eqn:Hval2.
      * (* t2 is already a value *)
        simpl stepf in Hstep.
        destruct t1; try solve_by_invert.
        ** destruct (is_value t2) eqn:Hval2' in Hstep; try (rewrite Hval2' in Hval2; inversion Hval2).
           apply in_inv in Hstep. destruct Hstep; try solve_by_invert.
           rewrite <- H. apply ST_AppAbs. apply is_value__value. assumption.
        ** solve_app_val12 n t2 Hstep Hval1 Hval2.
        ** solve_app_val12 <{ inl t t1 }> t2 Hstep Hval1 Hval2.
        ** solve_app_val12 <{ inr t t1 }> t2 Hstep Hval1 Hval2.
        ** solve_app_val12 <{ nil t }> t2 Hstep Hval1 Hval2.
        ** solve_app_val12_pair <{ t1_1 :: t1_2 }> t2 Hstep Hval1 Hval2.
        ** solve_app_val12 <{ unit }> t2 Hstep Hval1 Hval2.
        ** solve_app_val12_pair <{ (t1_1, t1_2) }> t2 Hstep Hval1 Hval2.
      * (* t2 is not a value, but t1 is *)
        simpl stepf in Hstep.
        destruct t1; try solve_by_invert; try solve_app_val1_nval2 t2 Hstep Hval1 Hval2 IHt2.
        ** solve_app_val1_nval2_pair <{ inl t t1 }> t2 Hstep Hval1 Hval2 IHt1 IHt2.
        ** solve_app_val1_nval2_pair <{ inr t t1 }> t2 Hstep Hval1 Hval2 IHt1 IHt2.
        ** solve_app_val1_nval2_pair <{ t1_1 :: t1_2 }> t2 Hstep Hval1 Hval2 IHt1 IHt2.
        ** solve_app_val1_nval2_pair <{ (t1_1, t1_2) }> t2 Hstep Hval1 Hval2 IHt1 IHt2.
    + (* t1 is not a value *)
        simpl stepf in Hstep.
        destruct t1; try solve_by_invert.
      * solve_app_nval1 <{ t1_1 t1_2 }> Hstep Hval1 IHt1.
      * solve_app_nval1 <{ succ t1 }> Hstep Hval1 IHt1.
      * solve_app_nval1 <{ pred t1 }> Hstep Hval1 IHt1.
      * solve_app_nval1 <{ t1_1 * t1_2 }> Hstep Hval1 IHt1.
      * solve_app_nval1 <{ if0 t1_1 then t1_2 else t1_3 }> Hstep Hval1 IHt1.
      * solve_app_nval1 <{ inl t t1 }> Hstep Hval1 IHt1.
      * solve_app_nval1 <{ inr t t1 }> Hstep Hval1 IHt1.
      * solve_app_nval1 <{ case t1_1 of | inl s => t1_2 | inr s0 => t1_3 }> Hstep Hval1 IHt1.
      * solve_app_nval1 <{ t1_1 :: t1_2 }> Hstep Hval1 IHt1.
      * solve_app_nval1 <{ case t1_1 of | nil => t1_2 | s :: s0 => t1_3 }> Hstep Hval1 IHt1.
      * solve_app_nval1 <{ (t1_1, t1_2) }> Hstep Hval1 IHt1.
      * solve_app_nval1 <{ t1.fst }> Hstep Hval1 IHt1.
      * solve_app_nval1 <{ t1.snd }> Hstep Hval1 IHt1.
      * solve_app_nval1 <{ let s = t1_1 in t1_2 }> Hstep Hval1 IHt1.
      * solve_app_nval1 <{ fix t1 }> Hstep Hval1 IHt1.
      * solve_app_nval1 <{ t1_1 !! t1_2 }> Hstep Hval1 IHt1.
  - (* mult *)
    intros t' Hstep.
    simpl in Hstep.
    destruct (t1); try solve_by_invert; try solve_mul_nval t2 Hstep IHt1.
    + destruct (t2); try solve_by_invert.
      * solve_mul_nval <{ t3 t4 }> Hstep IHt2.
      * apply in_inv in Hstep;
        destruct Hstep;
        try solve_by_invert;
        rewrite <- H;
        eauto.
      * solve_mul_nval <{ succ t }> Hstep IHt2.
      * solve_mul_nval <{ pred t }> Hstep IHt2.
      * solve_mul_nval <{ t3 * t4 }> Hstep IHt2.
      * solve_mul_nval <{ if0 t3 then t4 else t5 }> Hstep IHt2.
      * solve_mul_nval <{ inl t t0 }> Hstep IHt2.
      * solve_mul_nval <{ inr t t0 }> Hstep IHt2.
      * solve_mul_nval <{ case t3 of | inl s => t4 | inr s0 => t5 }> Hstep IHt2.
      * solve_mul_nval <{ t3 :: t4 }> Hstep IHt2.
      * solve_mul_nval <{ case t3 of | nil => t4 | s :: s0 => t5 }> Hstep IHt2.
      * solve_mul_nval <{ (t3, t4) }> Hstep IHt2.
      * solve_mul_nval <{ t.fst }> Hstep IHt2.
      * solve_mul_nval <{ t.snd }> Hstep IHt2.
      * solve_mul_nval <{ let s = t3 in t4 }> Hstep IHt2.
      * solve_mul_nval <{ fix t }> Hstep IHt2.
      * solve_mul_nval <{ t3 !! t4 }> Hstep IHt2.
    + solve_mul_nval_pair <{ inl t t0 }> t2 Hstep IHt2.
    + solve_mul_nval_pair <{ inr t t0 }> t2 Hstep IHt2.
    + solve_mul_nval_pair <{ t3 :: t4 }> t2 Hstep IHt2.
    + solve_mul_nval_pair <{ (t3, t4) }> t2 Hstep IHt2.
  - (* if0 *)
    intros t' Hstep.
    simpl in Hstep.
    destruct (is_value t1).
    destruct t1; try solve_by_invert.
    + destruct n; apply in_inv in Hstep; destruct Hstep; try inversion H; eauto.
    + apply in_map_iff in Hstep;
      destruct Hstep as [x Hstep];
      destruct Hstep as [Ht' Hx];
      apply IHt1 in Hx;
      rewrite <- Ht';
      eauto.
  - (* case *)
    intros t' Hstep.
    simpl in Hstep.
    destruct t1; try solve_by_invert; try (
      apply in_map_iff in Hstep;
      destruct Hstep as [x Hstep];
      destruct Hstep as [Ht' Hx];
      apply IHt1 in Hx;
      rewrite <- Ht';
      eauto); try (
      destruct (is_value t1) eqn:Hval1; try (
       apply in_inv in Hstep; destruct Hstep; try inversion H; apply is_value__value in Hval1; eauto); try (
        apply in_map_iff in Hstep;
        destruct Hstep as [x Hstep];
        destruct Hstep as [Ht' Hx];
        apply IHt1 in Hx;
        rewrite <- Ht';
        eauto)).
  - (* cons *)
    intros t' Hstep.
    simpl in Hstep.
    destruct (is_value t1) eqn:Hval1.
    + destruct (is_value t2) eqn:Hval2. try inversion Hstep.
      apply in_map_iff in Hstep;
      destruct Hstep as [x Hstep];
      destruct Hstep as [Ht' Hx];
      apply IHt2 in Hx;
      rewrite <- Ht';
      apply is_value__value in Hval1.
      eauto.
    + apply in_map_iff in Hstep;
      destruct Hstep as [x Hstep];
      destruct Hstep as [Ht' Hx];
      apply IHt1 in Hx;
      rewrite <- Ht';
      eauto.
  - (* lcase *)
    intros t' Hstep.
    simpl in Hstep.
    destruct t1; try solve_by_invert; try (
      apply in_map_iff in Hstep;
      destruct Hstep as [x Hstep];
      destruct Hstep as [Ht' Hx];
      apply IHt1 in Hx;
      rewrite <- Ht';
      eauto).
    + apply in_inv in Hstep; destruct Hstep; try inversion H; eauto.
    + destruct (is_value t1_1 && is_value t1_2) eqn:Hval12.
      * apply andb_true_iff in Hval12.
        destruct Hval12 as [Hval1 Hval2].
        apply is_value__value in Hval1.
        apply is_value__value in Hval2.
        apply in_inv in Hstep; destruct Hstep; try inversion H; eauto.
      * apply in_map_iff in Hstep;
        destruct Hstep as [x Hstep];
        destruct Hstep as [Ht' Hx];
        apply IHt1 in Hx;
        rewrite <- Ht';
        eauto.
  - (* pair *)
    intros t' Hstep.
    simpl in Hstep.
    destruct (is_value t1) eqn:Hval1.
    + destruct (is_value t2) eqn:Hval2. try inversion Hstep.
      apply in_map_iff in Hstep;
      destruct Hstep as [x Hstep];
      destruct Hstep as [Ht' Hx];
      apply IHt2 in Hx;
      rewrite <- Ht';
      apply is_value__value in Hval1.
      eauto.
    + apply in_map_iff in Hstep;
      destruct Hstep as [x Hstep];
      destruct Hstep as [Ht' Hx];
      apply IHt1 in Hx;
      rewrite <- Ht';
      eauto.
  - (* fst *)
    intros t' Hstep.
    simpl in Hstep.
    destruct (is_value t) eqn:Hval.
    + destruct t; try solve_by_invert.
      apply in_inv in Hstep; destruct Hstep; try inversion H.
      rewrite H in Hval.
      inversion Hval.
      apply andb_true_iff in H2; destruct H2 as [Ht1 Ht2].
      apply is_value__value in Ht1.
      apply is_value__value in Ht2.
      eauto.
    + apply in_map_iff in Hstep;
      destruct Hstep as [x Hstep];
      destruct Hstep as [Ht' Hx];
      apply IHt in Hx;
      rewrite <- Ht';
      eauto.
  - (* snd *)
    intros t' Hstep.
    simpl in Hstep.
    destruct (is_value t) eqn:Hval.
    + destruct t; try solve_by_invert.
      apply in_inv in Hstep.
      destruct Hstep; try inversion H.
      rewrite H in Hval.
      inversion Hval.
      apply andb_true_iff in H2; destruct H2 as [Ht1 Ht2].
      apply is_value__value in Ht1.
      apply is_value__value in Ht2.
      eauto.
    + apply in_map_iff in Hstep;
      destruct Hstep as [x Hstep];
      destruct Hstep as [Ht' Hx];
      apply IHt in Hx;
      rewrite <- Ht';
      eauto.
  - (* let *)
    intros t' Hstep.
    simpl in Hstep.
    destruct (is_value t1) eqn:Hval1.
    + apply in_inv in Hstep;
      destruct Hstep; try inversion H;
      apply is_value__value in Hval1;
      eauto.
    + apply in_map_iff in Hstep;
      destruct Hstep as [x Hstep];
      destruct Hstep as [Ht' Hx];
      apply IHt1 in Hx;
      rewrite <- Ht';
      eauto.
  - (* non determinism *)
    intros t' Hstep.
    simpl in Hstep.
    destruct Hstep as [H1 | H2 ].
    + rewrite H1. eauto.
    + destruct H2 as [H2 | HFalse]; try contradiction.
      rewrite H2. eauto.
Qed.

(* TODO *)
(* Completeness of [stepf]. *)
Theorem complete_stepf : forall t t',
    t --> t'  ->  In t' (stepf t).
Proof. (* TODO *) Admitted.


End StepFunction.
(** [] *)

Fixpoint big_stepf (t : tm) : list tm :=
  match t with
  (* pure STLC *)
  (* If, at the point when this is being evaluated, it hasn't yet been substituted,
     then this variable is unassigned, and we error out (with the empty list *)
  | tm_var y => []
  | <{\y:T, t1}> => [t]
  | <{t1 t2}> => fold_right (fun x1 acc1 => match x1 with
                                            | <{\y:T, tt1}> => (fold_right
                                                    (fun x2 acc2 => stepf <{[y:=x2]tt1}> ++ acc2)
                                                    (stepf t2) [])
                                                    ++ acc1
                                            | _ => acc1
                                            end) (stepf t1) []

  (* numbers *)
  | tm_const _ => [t]
  | <{ succ t1 }> =>
    fold_right (fun x acc => match x with
                                 | tm_const v =>  tm_const (v + 1) :: acc
                                 | _ => acc
                                end ) (stepf t1) []


  | <{ pred t1 }> =>
    fold_right (fun x acc => match x with
                                 | tm_const v =>  tm_const (v - 1) :: acc
                                 | _ => acc
                                end ) (stepf t1) []

  | <{ t1 * t2 }> =>
    fold_right (fun x1 acc1 => match x1 with
                               | tm_const v1 =>
                                   (fold_right (fun x2 acc2 => match x2 with
                                                               | tm_const v2 =>  tm_const (v1 * v2) :: acc2
                                                               | _ => acc2
                                                               end)
                                                               (stepf t2) []) ++ acc1
                               | _ => acc1
                               end ) (stepf t1) []
  | <{if0 t1 then t2 else t3}> => fold_right (fun x acc => match x with
                                                           | tm_const 0 => (stepf t2) ++ acc
                                                           | tm_const _ => (stepf t3) ++ acc
                                                           | _ => acc
                                                           end) (stepf t1) []

  (* sums *)
  | <{inl T2 t1}> => map (fun x => <{inl T2 x}>) (stepf t1)
  | <{inr T1 t2}> => map (fun x => <{inr T1 x}>) (stepf t2)
  | <{case t0 of | inl y1 => t1 | inr y2 => t2}> => fold_right (fun t acc =>
        match t with
        | <{ inl T2 tt1 }> => (stepf <{[y1:=tt1]t1}>) ++ acc
        | <{ inr T1 tt2 }> => (stepf <{[y2:=tt2]t2}>) ++ acc
        | _ => acc
        end) (stepf t0) []

  (* lists *)
  | <{nil _}> => [t]
  | <{t1 :: t2}> => fold_right
                    (fun x2 acc2 => match x2 with
                                    | <{ nil T }> => fold_right (fun x1 acc1 => <{ x1 :: x2 }> :: acc2 ) (stepf t1) []
                                    | <{ h::tail }> => fold_right (fun x1 acc1 => <{ x1 :: x2 }> :: acc2 ) (stepf t1) []
                                    | _ => acc2
                                    end)
                    (stepf t2) []
  | <{case t1 of | nil => t2 | y1 :: y2 => t3}> => fold_right (fun t acc =>
        match t with
        | <{ nil _ }> => (stepf t2) ++ acc
        | <{ tt1 :: tt2 }> => (stepf <{[y1:=tt1]([y2:=tt2]t2)}>) ++ acc
        | _ => acc
        end) (stepf t1) []

  (* unit *)
  | <{unit}> => [t]

  (* pairs *)
  | <{(t1 , t2)}> => fold_right (fun x1 acc1 => (map (fun x2 => <{(x1, x2)}>) (stepf t2)) ++ acc1) (stepf t1) []
  | <{t.fst}> => fold_right (fun x acc => match x with
                                          | <{ (v1, _) }> => v1::acc
                                          | _ => acc
                                          end) (stepf t) []
  | <{t.snd}> => fold_right (fun x acc => match x with
                                            | <{ (_, v2) }> => v2::acc
                                            | _ => acc
                                            end) (stepf t) []

  (* let *)
  | <{let y = t1 in t2}> => fold_right (fun x1 acc1 => (stepf <{[y:=x1]t2}>) ++ acc1) (stepf t1) []

  (* fix *)
  | <{ fix t' }> => [t']

  (* non-deterministic choice *)
  | <{t1 !! t2}> => (stepf t1) ++ (stepf t2)
  end.
  (* sums *)
  | <{inl T2 t1}> => map (fun x => <{inl T2 x}>) (stepf t1)
  | <{inr T1 t2}> => map (fun x => <{inr T1 x}>) (stepf t2)
  | <{case t0 of | inl y1 => t1 | inr y2 => t2}> => fold_right (fun t acc =>
        match t with
        | <{ inl T2 tt1 }> => (stepf <{[y1:=tt1]t1}>) ++ acc
        | <{ inr T1 tt2 }> => (stepf <{[y2:=tt2]t2}>) ++ acc
        | _ => acc
        end) (stepf t0) []

  (* lists *)
  | <{nil _}> => [t]
  | <{t1 :: t2}> => fold_right
                    (fun x2 acc2 => match x2 with
                                    | <{ nil T }> => fold_right (fun x1 acc1 => <{ x1 :: x2 }> :: acc2 ) (stepf t1) []
                                    | <{ h::tail }> => fold_right (fun x1 acc1 => <{ x1 :: x2 }> :: acc2 ) (stepf t1) []
                                    | _ => acc2
                                    end)
                    (stepf t2) []
  | <{case t1 of | nil => t2 | y1 :: y2 => t3}> => fold_right (fun t acc =>
        match t with
        | <{ nil _ }> => (stepf t2) ++ acc
        | <{ tt1 :: tt2 }> => (stepf <{[y1:=tt1]([y2:=tt2]t2)}>) ++ acc
        | _ => acc
        end) (stepf t1) []

  (* unit *)
  | <{unit}> => [t]

  (* pairs *)
  | <{(t1 , t2)}> => fold_right (fun x1 acc1 => (map (fun x2 => <{(x1, x2)}>) (stepf t2)) ++ acc1) (stepf t1) []
  | <{t.fst}> => fold_right (fun x acc => match x with
                                          | <{ (v1, _) }> => v1::acc
                                          | _ => acc
                                          end) (stepf t) []
  | <{t.snd}> => fold_right (fun x acc => match x with
                                            | <{ (_, v2) }> => v2::acc
                                            | _ => acc
                                            end) (stepf t) []

  (* let *)
  | <{let y = t1 in t2}> => fold_right (fun x1 acc1 => (stepf <{[y:=x1]t2}>) ++ acc1) (stepf t1) []

  (* fix *)
  | <{ fix t' }> => [t']

  (* non-deterministic choice *)
  | <{t1 !! t2}> => (stepf t1) ++ (stepf t2)
  end.

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


