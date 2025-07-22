import Mathlib.Tactic

lemma not_left_in_right {s₁ s₂ : Type} (i : s₁ ⊕ s₂) (h : ¬ ∃ y:s₁, i = Sum.inl y) 
  [DecidableEq s₁] [DecidableEq s₂] : ∃ z:s₂, i = Sum.inr z := by 
  match i with 
  | Sum.inr x => use x
  | Sum.inl y => 
     exfalso
     apply h
     use y
