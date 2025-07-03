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
      simp
      sorry
    · simp
      intro h₅
      sorry

lemma union_span' (n m :ℕ) (W₁ W₂ : Submodule k V) (s₁ s₂ : Set V)
  (h₁:∀ x∈ s₁, s ∈ W₁) (h₂:∀ x∈s₂, s∈ W₂)
  (hs₁: W₁ = Submodule.span k s₁)
  (hs₂: W₂ = Submodule.span k s₂)
  (hw: ⊤ = W₁ ⊔ W₂)
  : ⊤ = Submodule.span k (s₁ ∪ s₂) := by
    ext v
    rw[hw]
    rw[Submodule.mem_sup]
    constructor
    · intro h₃
      rw[Submodule.span_union]
      rw[← hs₁]
      rw[← hs₂]
      rw[← hw]
      trivial
    · intro h₃
      rw[Submodule.span_union] at h₃
      rw[← hs₁] at h₃
      rw[← hs₂] at h₃
      rw[← Submodule.mem_sup]
      exact h₃


#check Submodule.mem_sup
    --intro X h₄
    --simp at h₄
    -- rw[Submodule.span_union
