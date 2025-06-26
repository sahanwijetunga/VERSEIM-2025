
import Mathlib.Tactic

import Mathlib.Data.FinEnum

#check FinEnum

example (n m :ℕ) : FinEnum ((Fin n) ⊕ (Fin m)) := inferInstance

#check FinEnum.card
#eval FinEnum.card ((Fin 15) ⊕ (Fin 3))


#check @FinEnum.equiv ((Fin 15) ⊕ (Fin 3))


example : (Fin 3) ⊕ (Fin 5) ≃ Fin 8 := 
  FinEnum.equiv

example : Nat.card (Fin 5) = FinEnum.card (Fin 5) := by simp

lemma replace (X:Type) [FinEnum X]  : Nat.card X = FinEnum.card X := by 
  refine Eq.symm (Nat.eq_of_beq_eq_true ?_) 



example (n m : ℕ) : FinEnum.card ((Fin n) ⊕ (Fin m)) = n + m := by 
  have hn : n = FinEnum.card (Fin n) := Eq.symm FinEnum.card_fin 
  have hm : m = FinEnum.card (Fin m) := Eq.symm FinEnum.card_fin 
  apply Eq.symm
  nth_rw 1 [ hn , hm ]
  apply Eq.symm
  rw [ <-replace n, <-replace m ]
  refine Nat.card_sum (α:= Fin n) (β := Fin m)
  
  
lemma f : FinEnum.card (Fin n) = n := by simp

#print f

example (n m : ℕ) : (Fin n) ⊕ (Fin m) ≃ Fin (n+m)  := by
   have : n+m = FinEnum.card ((Fin n) ⊕ (Fin m)) := by 
    


open Sum
def fin_disjoint_fin_equiv_fin (n m: ℕ) : (Fin n) ⊕ (Fin m) ≃ Fin (n+m) where
  toFun := fun i => 
    match i with
    | inl x => Fin.castAdd m x
    | inr x => by
        rw [ add_comm ] 
        exact Fin.castAdd n x 
  invFun := by 
    rintro ⟨i,_⟩
    if h : i < n then 
       have : NeZero n := NeZero.mk (by linarith)
       exact inl (Fin.ofNat n i)
    else
       have : NeZero m := NeZero.mk (by linarith)
       exact inr (Fin.ofNat m (n-i))
  left_inv := by sorry
  right_inv := by sorry



-- 
