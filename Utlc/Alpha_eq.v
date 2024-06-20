Require Import Nat.
Require Import List.
Require Import UTLC.LC.

Fixpoint count_fv_from (t : LC) (fv_list : list nat) : nat * list nat.
Proof.
  destruct t as [var | [t1 t2] | t'].
  - remember (existsb (fun x => x =? var) fv_list) as b.
    exact (if b then 0 else 1, if b then fv_list else var :: fv_list). 
  - remember (count_fv_from t1 fv_list) as left_f.
    remember (count_fv_from t2 (snd left_f)) as right_f.
    exact (fst left_f + fst right_f ,  snd right_f). 
  - remember (map S fv_list) as lifted_fv_list.
    exact ( fst (count_fv_from t' lifted_fv_list) , fv_list).
Qed.

Definition nb_fv (t : LC) : nat := fst (count_fv_from t nil).

Fixpoint well_formed_from (t : LC) (n : nat) : Prop .
Proof.
  destruct t as [var | [t1 t2] | t'].
  - exact (var <= n /\ 1 <= var).
  - exact ((well_formed_from t1 n) /\ (well_formed_from t2 (nb_fv t1))). 
  - exact (well_formed_from t' (S n)).
Qed.

Definition well_formed : LC -> Prop.
Proof.
  intro t.
  exact (well_formed_from t 1).
Qed.
  
Definition WLC : Set := {t : LC | well_formed t}.
 
