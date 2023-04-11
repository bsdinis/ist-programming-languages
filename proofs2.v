Theorem thm_simpl1: forall (a b c: nat),
  a = 0 ->  b * (a+b) = b * b.

Proof.
  intros.
  rewrite -> H.
  simpl.
  reflexivity.
Qed.

Theorem thm_simpl2: forall (a b c d: nat) (f: nat -> nat -> nat),
  a = b -> c = d -> (forall x y, f x y = f y x) -> f a c = f d b.

Proof.
  intros.
  rewrite -> H.
  rewrite -> H0.
  rewrite -> H1.
  reflexivity.
Qed.


Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.

Proof.
  intros.
  rewrite -> H.
  rewrite -> H.
  reflexivity.
Qed.

Lemma double_neg: forall b: bool,
  negb (negb b) = b.

Proof.
  intros.
  destruct b; simpl; reflexivity.
Qed.

Theorem negation_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = negb x) ->
  forall (b : bool), f (f b) = b.

Proof.
  intros.
  rewrite -> H.
  rewrite -> H.
  rewrite -> double_neg.
  reflexivity.
Qed.
