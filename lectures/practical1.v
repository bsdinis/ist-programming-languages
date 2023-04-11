
(* Exercise 1

   Define leb with type nat -> nat -> bool
   which tests whether the first argument is less than or equal than the second
 *)
Fixpoint leq(n m : nat) : bool :=
  match n with
  | 0 => true
  | S n' => match m with
            | 0 => false
            | S m' => leq n' m'
            end
  end.

Check leq.

Compute leq 0 0.
Compute leq 2 0.
Compute leq 0 2.
Compute leq 2 2.

Compute leq 3 7.


(* Exercise 2: Pairs of Numbers *)

Inductive natprod : Type :=
  | pair: nat -> nat -> natprod.

Notation "( x , y )" := (pair x y).

Compute (1, 2).

Definition fst(p: natprod) : nat :=
  match p with
  | (pair f _) => f
  end.

Definition snd(p: natprod) : nat :=
  match p with
  | (pair _ s) => s
  end.

Notation "x .0" := (fst x) (at level 100).
Notation "x .1" := (snd x) (at level 100).

(* Exercise 3: Proving swap_twice *)

Definition swap_pair (p: natprod) : natprod :=
  match p with
  | (m,n) => (n,m)
  end.

Lemma swap_twice: forall (m n: nat),
  swap_pair (swap_pair (m, n)) = (m, n).

Proof.
  intros.
  simpl.
  reflexivity.
Qed.

(* Exercise 4: Proving snd_fst_is_swap *)

Theorem snd_fst_is_swap: forall (p: natprod),
    (snd p, fst p) = swap_pair p.

Proof.
    intros.
    destruct p.
    simpl.
    reflexivity.
Qed.

