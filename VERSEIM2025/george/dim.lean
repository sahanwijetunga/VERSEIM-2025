import Mathlib.Tactic

variable {k V : Type} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]

--open Module



example ( W : Submodule k V) (s:Set W) : Set V :=  by
  exact { x:V | x ∈ W}

example (W:Submodule k V) (w:W) : V := ↑w

def f {n m:ℕ} {W₁ W₂ : Submodule k V} (s₁:Fin n →  W₁) (s₂: Fin m → W₂) :
  (Fin n) ⊕ (Fin m) → V := by
    intro i
    match i with
     | Sum.inl x => exact ↑(s₁ x)
     | Sum.inr y => exact ↑(s₂ y)

lemma union_span (n m:ℕ) (W₁ W₂ : Submodule k V) (s₁:Fin n →  W₁) (s₂: Fin m → W₂) 
      (h₁:(⊤:Submodule k W₁) = Submodule.span k (s₁ '' ⊤))
      (h₂:(⊤:Submodule k W₂) = Submodule.span k (s₂ '' ⊤))
      (h₃:⊤ = W₁ ⊔ W₂)
    : (⊤:Submodule k V) = Submodule.span k ((f s₁ s₂) '' ⊤)  := by sorry



lemma union_span' (n m :ℕ) (W₁ W₂ : Submodule k V) (s₁ s₂ : Set V)
  (h₁:∀ x∈ s₁, s ∈ W₁) (h₂:∀ x∈s₂, s∈ W₂)
  (hs₁: W₁ = Submodule.span k s₁)
  (hs₂: W₂ = Submodule.span k s₂)
  (hw: ⊤ = W₁ ⊔ W₂)
  : ⊤ = Submodule.span k (s₁ ∪ s₂) := by  sorry
