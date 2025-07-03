import Mathlib.Tactic

variable {k V : Type} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]

--open Module



example ( W : Submodule k V) (s:Set W) : Set V :=  by
  exact { x:V | x ∈ W}

example (W:Submodule k V) (w:W) : V := ↑w


-- f is defined up here for this problem

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
    : (⊤:Submodule k V) = Submodule.span k ((f s₁ s₂) '' ⊤)  := by
    have h₄ : W₁ + W₂ = ⊤ := by
      simp
      rw[h₃]
    ext v
    rw[h₃]
    rw[Submodule.mem_sup]
    constructor
    · intro h₅ --x₀-- h₆
      unfold f

      sorry
    · sorry


    --intro X h₄
    --simp at h₄
    -- rw[Submodule.span_union
