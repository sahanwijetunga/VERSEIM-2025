
import Mathlib.Tactic

import Mathlib.Data.FinEnum

example (n m :ℕ) : FinEnum ((Fin n) ⊕ (Fin m)) := inferInstance

lemma card_eq_finenum_card (X:Type) [FinEnum X]  : Nat.card X = FinEnum.card X := by 
  rw [ Nat.card_eq_fintype_card ]
  exact Eq.symm FinEnum.card_eq_fintypeCard 

lemma size_of_sum (n m : ℕ) : FinEnum.card ((Fin n) ⊕ (Fin m)) = n + m := by 
  have hn : n = FinEnum.card (Fin n) := Eq.symm FinEnum.card_fin 
  have hm : m = FinEnum.card (Fin m) := Eq.symm FinEnum.card_fin 
  
  suffices : FinEnum.card (Fin n) + FinEnum.card (Fin m) = FinEnum.card (Fin n ⊕ Fin m) := by sorry

  apply Eq.symm
  nth_rw 1 [ hn , hm ]
  apply Eq.symm
  rw [ ← card_eq_finenum_card (Fin n), 
       ← card_eq_finenum_card (Fin m), 
       ← card_eq_finenum_card ((Fin n) ⊕ (Fin m)) ]
  apply Nat.card_sum 
  
 
example (n m : ℕ) : (Fin n) ⊕ (Fin m) ≃ Fin (n+m)  := by
   rw [ ← size_of_sum]
   exact FinEnum.equiv
    

