Inductive LC : Type :=
| Var : nat -> LC
| App : LC * LC -> LC
| Abs : LC -> LC
.

Section Ex.

Definition Id : LC :=  Abs (Var 1).

Definition K : LC := Abs (Abs (Var 2)).

Definition K' : LC := Abs (Abs (Var 1)).

Definition S : LC := Abs (Abs (Abs (App ((App (Var 3 , Var 1)), (App (Var 2 , Var 1)))))).

Definition ω : LC := Abs (App (Var 1, Var 1)).

Definition Ω : LC := App (ω, ω). 

Definition Y : LC := Abs (App (Abs (App ( Var 2, App (Var 1, Var 1))) , Abs (App ( Var 2, App (Var 1, Var 1))))).

End Ex.
