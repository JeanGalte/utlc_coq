Inductive LC : Type :=
| Var : nat -> LC
| App : LC * LC -> LC
| Abs : LC -> LC
.                
