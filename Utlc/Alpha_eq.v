Require Import Nat.
Require Import UTLC.LC.

(*
α-equivalence is syntactic equality for the representation with De Bruijin indexes, under the following naming convention when building terms :

1) We start free variable indexes right after the number of binders.
2) We start counting variables from 1.  

*)

Fixpoint nb_binders (t : LC) : nat.
Proof.
  destruct t as [var | [t1 t2] | t'].
  - exact 0.
  - exact (nb_binders t1).
  - exact (1 + nb_binders t').
Qed.

Fixpoint count_fv_from (t : LC) (n : nat) : nat.
Proof.
  destruct t as [var | [t1 t2] | t'].
  - exact (if var <=? n then 0 else 1).
  - exact (count_fv_from t2 (count_fv_from t1 n)). 
  - exact (count_fv_from t' (n+1)).
Qed.

Definition nb_fv (t : LC) : nat := count_fv_from t 0.

Fixpoint min_var (t : LC) : nat.
Proof.
  destruct t as [var | [t1 t2] | t'].
  - exact var.
  - exact (min (min_var t1) (min_var t2)).
  - exact (min_var t').
Qed.  

Fixpoint max_var (t : LC) : nat.
Proof.
  destruct t as [var | [t1 t2] | t'].
  - exact var.
  - exact (max (max_var t1) (max_var t2)).
  - exact (max_var t').
Qed.
