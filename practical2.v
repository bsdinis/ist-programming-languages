Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Import ListNotations.
Import Notations.

Fixpoint tl {T: Type} (l: list T) : list T :=
  match l with
  | [] => []
  | h :: t => t
  end.

Compute tl [1;2;3].

Fixpoint removelast {T: Type} (l: list T) : list T :=
  match l with
  | [] => []
  | [_] => []
  | h :: t => h :: (removelast t)
  end.


Compute removelast [1;2;3].

Fixpoint firstn {T: Type} (n: nat) (l: list T) : list T :=
  match n, l with
  | 0, _ => []
  | _, [] => []
  | (S n'), (h :: t) => h :: (firstn n' t)
  end.

Compute firstn 0 [2;3;4].
Compute firstn 5 [].
Compute firstn 0 [].
Compute firstn 4 [2;3].
Compute firstn 4 [2;3;4;5;6].

Fixpoint skipn {T: Type} (n: nat) (l: list T) : list T :=
  match n, l with
  | 0, l => l
  | _, [] => []
  | (S n'), (h :: t) => skipn n' t
  end.

Compute skipn 0 [2;3;4].
Compute skipn 5 [].
Compute skipn 0 [].
Compute skipn 4 [2;3].
Compute skipn 4 [2;3;4;5;6].

Fixpoint last {T: Type} (l : list T) : option T :=
  match l with
  | [] => None
  | [e] => Some e
  | _ :: t => (last t)
  end.

Compute last [2;3;4].
Compute last [].
Compute last [].
Compute last [2;3].
Compute last [2;3;4;5;6].

Fixpoint seq (start len: nat) : (list nat) :=
  match len with
  | 0 => []
  | S l' => start :: (seq (start + 1) l')
  end.

Compute seq 3 4.
Compute seq 3 0.
Compute seq 3 6.

Definition split {T U: Type} (l: list (T * U)) : (list T) * (list U) :=
  (map (fun p => match p with | (t, _) => t end)  l,
   map (fun p => match p with | (_, u) => u end)  l).

Check split.
Compute split [(1,true);(2,false);(3,true)].

Fixpoint append {T: Type} (l1 l2: list T) : list T :=
  match l1, l2 with
  | [], _ => l2
  | _, [] => l1
  | (h::t), l2 => h:: (append t l2)
  end.

Compute append [1;2;3] [4;5;6].

Definition rev {T: Type} (l: list T) : list T :=
  fold_left (fun x y =>  (cons y x) ) l []  .

Definition revr {T: Type} (l: list T) : list T :=
  fold_right (fun x y =>  (append y [x])) [] l .

Print fold_left.
Compute rev [1;2;3].
Compute revr [1;2;3].

Definition existsb {T: Type} (pred: T -> bool) (l: list T) : bool :=
  1 <=? length (filter  pred l).

Compute existsb (fun e => e <=? 3) [2;4;5].


Definition forallb {T: Type} (pred: T -> bool) (l: list T) : bool :=
  length l =? length (filter  pred l).

Compute forallb (fun e => e <=? 3) [2;4;5].
Compute forallb (fun e => e <=? 3) [2;2;2].

Definition find {T: Type} (pred: T -> bool) (l: list T) : option T :=
  fold_right (fun x y => Some x) None (filter pred l) .

Compute find (fun e => e <=? 3) [6;4;1;3;7].
Compute find (fun e => e <=? 3) [6;4;4;5;7].

(* exercise 2 *)

Definition partition {T: Type} (pred: T -> bool) (l: list T) : (list T) * (list T) :=
  ( filter pred l , filter (fun x => negb (pred x)) l).

Compute partition (fun e => e <=? 3) [6;4;1;3;7].

Definition list_prod {T U: Type} (l1: list T) (l2: list U) : (list (T * U)) :=
  fold_right append [] (map (fun t => (map (fun u => (t, u)) l2)) l1).

Compute list_prod [1; 2] [true; false].

Definition length {T: Type} (l: list T) : nat :=
  fold_right (fun x y => S y ) 0 l.

Compute length [].
Compute length [1;2;3].

Definition forallb' {T: Type} (pred: T -> bool) (l: list T) : bool :=
  fold_right (fun x y => andb x y) true (map pred l).

Compute forallb' (fun e => e <=? 3) [2;4;5].
Compute forallb' (fun e => e <=? 3) [2;2;2].


(* exercise 3 *)


Theorem thm_simpl1: forall (a b c: nat),
  a = 0 -> (mult b (a+b)) = (mult b b).

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
