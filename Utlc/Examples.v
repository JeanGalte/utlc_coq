Require Import Nat.
Require Import List.
Require Import UTLC.LC.
Require Import UTLC.Alpha_eq.


Definition Id : LC :=  Abs (Var 1).
  
Definition K : LC := Abs (Abs (Var 2)).

Definition K' : LC := Abs (Abs (Var 1)).

Definition S : LC := Abs (Abs (Abs (App ((App (Var 3 , Var 1)), (App (Var 2 , Var 1)))))).

Definition ω : LC := Abs (App (Var 1, Var 1)).

Definition Ω : LC := App (ω, ω). 

Definition Y : LC := Abs (App (Abs (App ( Var 2, App (Var 1, Var 1))) , Abs (App ( Var 2, App (Var 1, Var 1))))).

Definition Id_WLC : WLC.
Proof.
  exists Id.
  unfold well_formed ; unfold well_formed_from.
  simpl.
  auto.
Defined.

Definition K_WLC : WLC.
Proof.
  exists K.
  unfold well_formed ; unfold well_formed_from.
  simpl.
  auto.
Defined.

Definition K'_WLC : WLC.
Proof.
  exists K'.
  unfold well_formed ; unfold well_formed_from.
  simpl.
  auto.
Defined.

Definition S_WLC : WLC.
Proof.
  exists S.
  unfold well_formed ; unfold well_formed_from ; unfold nb_fv ; unfold count_fv_from.
  simpl.
  auto 6.
Defined.

Definition ω_WLC : WLC.
Proof.
  exists ω.
  unfold well_formed ; unfold well_formed_from.
  simpl.
  auto.
Defined.

Definition Ω_WLC : WLC.
Proof.
  exists Ω.
  unfold well_formed ; unfold well_formed_from.
  simpl.
  auto.
Defined.

Definition Y_WLC : WLC.
Proof.
  exists Y.
  unfold well_formed ; unfold well_formed_from.
  simpl.
  auto.
Defined. 
