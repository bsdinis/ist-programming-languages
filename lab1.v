(* Exercise 1 *)

Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.


Definition weekday_to_nat (d : day) : nat :=
  match d with
  |  sunday	    => 1
  |  monday     => 2
  |  tuesday	  => 3
  |  wednesday	=> 4
  |  thursday	  => 5
  |  friday	    => 6
  |  saturday	  => 7
  end.

Check weekday_to_nat monday.
Compute weekday_to_nat sunday.

Definition is_weekend (d : day) : bool :=
  match d with
  |  sunday|saturday => false
  |  _ => true
  end.


(* Exercise 2 *)

Definition negb (b: bool) : bool :=
  match b with
  | false => true
  | true => false
  end.

Example test_negb1: (negb true) = false.
Proof. auto. Qed.
Example test_negb2: (negb false) = true.
Proof. auto. Qed.


Definition andb (a b : bool) : bool :=
  match a with
  | false => false
  | true => b
  end.

Example test_andb1: (andb false false) = false.
Proof. auto. Qed.
Example test_andb2: (andb false true) = false.
Proof. auto. Qed.
Example test_andb3: (andb true false) = false.
Proof. auto. Qed.
Example test_andb4: (andb true true) = true.
Proof. auto. Qed.

Definition orb (a b : bool) : bool :=
  match a with
  | false => b
  | true => true
  end.

Example test_orb1: (orb false false) = false.
Proof. auto. Qed.
Example test_orb2: (orb false true) = true.
Proof. auto. Qed.
Example test_orb3: (orb true false) = true.
Proof. auto. Qed.
Example test_orb4: (orb true true) = true.
Proof. auto. Qed.

Definition xorb (a b : bool) : bool :=
  match a with
  | false => b
  | true => negb b
  end.

Notation "~ x" := (negb x).
Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).
Notation "x ^ y" := (xorb x y).

Example test_xorb1: (false  ^ false) = false.
Proof. auto. Qed.
Example test_xorb2: (false  ^ true) = true.
Proof. auto. Qed.
Example test_xorb3: (true   ^ false) = true.
Proof. auto. Qed.
Example test_xorb4: (true   ^ true) = false.
Proof. auto. Qed.


(* Exercise 3 *)

Module NatPlayground.

Fixpoint minustwo (n : nat) : nat :=
  match n with
  | S ( S n' ) => n'
  | _ => 0
  end.

Check minustwo.
Check minustwo 0.
Check minustwo 213.
Compute minustwo 0.
Compute minustwo 213.


Fixpoint evenb (n: nat) : bool :=
  match n with
  | 0 => true
  | 1 => false
  | S ( S n' ) => evenb n'
  end.

Compute evenb 234.
Compute evenb 231.

Definition oddb (n: nat) : bool :=
  ~(evenb n).

Compute evenb 234.
Compute evenb 231.

Fixpoint plus (m n: nat) : nat :=
  match m with
  | 0 => n
  | S m' => S ( plus m' n )
  end.

Compute plus 1 2.
Compute plus 0 0.
Compute plus 0 6.

Fixpoint mult (m n: nat) : nat :=
  match m with
  | 0 => 0
  | S m' => (plus n ( mult m' n ))
  end.

Compute mult 1 2.
Compute mult 0 0.
Compute mult 0 6.
Compute mult 3 6.

Fixpoint exp (m n: nat) : nat :=
  match n with
  | 0 => 1
  | S n' => (mult m ( exp m n' ))
  end.


Compute exp 1 2.
Compute exp 0 0.
Compute exp 0 6.
Compute exp 3 6.

(*

plus 3 2
S (plus 2 2)
S (S (plus 1 2) )
S (S (S (plus 0 2) ) )
S (S (S ( 2 ) ) )
S (S (3) )
S (4)
5
 *)

Fixpoint minus (m n: nat) : nat :=
  match m with
  | 0 => 0
  | S m' => match n with
            | 0 => m
            | S n' => minus m' n'
            end
  end.

Check minus.
Compute minus 0 0.
Compute minus 0 5.
Compute minus 5 0.
Compute minus 5 5.
Compute minus 10 5.

Inductive natpair: Type :=
  | pair : nat -> nat -> natpair.

Notation "( x , y )" := (pair x y).


Fixpoint minus' (m n: nat) : nat :=
  match (m, n) with
  | (0, _) => 0
  | (_, 0) => m
  | (S m', S n') => minus m' n'
  end.

Check minus'.
Compute minus' 0 0.
Compute minus' 0 5.
Compute minus' 5 0.
Compute minus' 5 5.
Compute minus' 10 5.

Fixpoint factorial (n: nat) : nat :=
  match n with
  | 0 => 1
  | S n' => mult n (factorial n')
  end.

Check factorial.
Compute factorial 0.
Compute factorial 1.
Compute factorial 5.

End NatPlayground.
