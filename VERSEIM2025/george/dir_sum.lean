import Mathlib.Tactic

variable (k V : Type) [Field k] [AddCommGroup V] [Module k V]

example (W₁ W₂ : Submodule k V) 
        (ι₁ ι₂ : Type) [Fintype ι₁] [Fintype ι₂]
        (B₁ : Basis ι₁ k W₁)
        (B₂ : Basis ι₂ k W₂) 
        (hspan : W₁ ⊔ W₂ = (⊤:Set V))
        (hindep : W₁ ⊓ W₂ = (⊥:Set V)) :
       Basis (ι₁ ⊕ ι₂) k V := by sorry
