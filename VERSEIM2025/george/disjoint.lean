import Mathlib.Tactic


variable {ι₁ ι₂ : Type}

def p (i:ι₁ ⊕ ι₂) : Prop :=
  ∃ y:ι₁ , i = Sum.inl y



lemma not_p_inr (x : ι₂) : ¬ p (Sum.inr x:ι₁⊕ι₂) := by
  unfold p
  by_contra h
  rcases h with ⟨y,hy⟩
  apply_fun Sum.isRight at hy
  simp at hy

lemma not_left_in_right {s₁ s₂ : Type} (i : s₁ ⊕ s₂) (h : ¬ ∃ y:s₁, i = Sum.inl y) 
  : ∃ z:s₂, i = Sum.inr z := by 
  match i with 
  | Sum.inr x => use x
  | Sum.inl y => 
     exfalso
     apply h
     use y

def eq : { i : ι₁ ⊕ ι₂ // ¬ p i } ≃ ι₂ where
  toFun := by
    intro ⟨i,hᵢ⟩
    match i with
    | Sum.inr z => exact z
    | Sum.inl y => 
       exfalso
       apply hᵢ
       use y
  invFun i := ⟨Sum.inr i, not_p_inr i⟩
  left_inv := by
     intro ⟨ i,hᵢ ⟩
     rcases (not_left_in_right i hᵢ) with ⟨j,hj⟩
     

  right_inv := by
     intro i
     

  
#check Sum.recOn

#check Nat.noConfusion
