Require Import Nat.
Require Import List.
Require Import UTLC.LC.
Require Import UTLC.Alpha_eq.


Definition Id : LC :=  Abs (Var 1).

Lemma well_formed_Id : well_formed Id.
Proof.
  unfold well_formed ; unfold well_formed_from.
  simpl.
  auto.
Qed.

Definition K : LC := Abs (Abs (Var 2)).

Definition K' : LC := Abs (Abs (Var 1)).

Definition S : LC := Abs (Abs (Abs (App ((App (Var 3 , Var 1)), (App (Var 2 , Var 1)))))).

Definition ω : LC := Abs (App (Var 1, Var 1)).

Definition Ω : LC := App (ω, ω). 

Definition Y : LC := Abs (App (Abs (App ( Var 2, App (Var 1, Var 1))) , Abs (App ( Var 2, App (Var 1, Var 1))))).

