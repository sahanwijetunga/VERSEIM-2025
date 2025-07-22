import Mathlib.Tactic

noncomputable section

variable {k:Type} [Field k]

variable {V₁ V₂ ι : Type} [AddCommGroup V₁] [AddCommGroup V₂]
         [Module k V₁] [Module k V₂]

-- `symm` gives the inverse of a linear equivalence, like so:

example (l: V₁ ≃ₗ[k] V₂) :  V₂ ≃ₗ[k] V₁ := l.symm

-- in mathlib, a basis of V indexed by ι amounts to a linear
-- equivalence between V and the space `ι →₀ k`.

-- for a basis b, b.repr is this linear equivalence:

example (b₁:Basis ι k V₁) : V₁ ≃ₗ[k] (ι →₀ k) := b₁.repr
example (b₂:Basis ι k V₂) : V₂ ≃ₗ[k] (ι →₀ k) := b₂.repr

-- so given bases of V₁ and V₂ indexed by the same type ι, we find a
-- linear equivalence between V₁ and V₂ by composing them

-- we can use `LinearEquiv.trans` for the composition.

def equiv_from_bases (b₁:Basis ι k V₁) (b₂:Basis ι k V₂) 
  : V₁ ≃ₗ[k] V₂ := 
  LinearEquiv.trans b₁.repr (b₂.repr.symm)


-- we can confirm that for each `i:ι`, this equivalence maps `b₁ i` to
-- `b₂ i`

example (b₁:Basis ι k V₁) (b₂:Basis ι k V₂) (i:ι) : 
  (equiv_from_bases b₁ b₂) (b₁ i) = b₂ i := by 
  unfold equiv_from_bases
  simp
