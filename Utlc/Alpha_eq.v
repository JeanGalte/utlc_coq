Require Import Nat.
Require Import List.
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

Fixpoint count_fv_from (t : LC) (fv_list : list nat) : nat * list nat.
Proof.
  destruct t as [var | [t1 t2] | t'].
  - remember (existsb (fun x => x =? var) fv_list) as b.
    exact (if b then 0 else 1, if b then fv_list else var :: fv_list). 
  - remember (count_fv_from t1 fv_list) as left_f.
    remember (count_fv_from t2 (snd left_f)) as right_f.
    exact (fst left_f + fst right_f ,  snd right_f). 
  - remember (map  (fun x => x+1) fv_list) as lifted_fv_list.
    exact ( fst (count_fv_from t' lifted_fv_list) , fv_list).
Qed.

Definition count_fv (t : LC) : nat := fst (count_fv_from t nil).
                                    
