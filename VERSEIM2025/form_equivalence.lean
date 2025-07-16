
import Mathlib.Tactic

open LinearMap
open LinearMap (BilinForm)

variable {k V₁ V₂ :Type} [Field k] 
  [AddCommGroup V₁] [Module k V₁]
  [AddCommGroup V₂] [Module k V₂]

variable { Φ:V₁ ≃ₗ[k] V₂ }

-- given the linear equivalence φ, here is how to get a basis of V₂ from a basis of V₁

example {ι : Type} [Fintype ι] (b:Basis ι k V₁) ( φ:V₁ ≃ₗ[k] V₂ ):
  Basis ι k V₂ := b.map φ


-- here is what it means for the pair (V₁,β₁) to be equivalent to
-- (V₂,β₂) :

structure equiv_of_spaces_with_form
  (β₁:BilinForm k V₁) 
  (β₂:BilinForm k V₂)
  where
    equiv : V₁ ≃ₗ[k] V₂
    compat : ∀ (x y : V₁), β₁ x y = β₂ (equiv v₁) (equiv v₂) 
  
-- the "target theorem" below says that the pair (V₁,β₁) is equivalent
-- to (V₂,β₂) if and only if there is a basis b₁ for V₁ and a basis b₂
-- for V₂ such that the matrix determined by b₁ and β₁ coincides with
-- the matrix determined by b₂ and β₂.

-- to prove →, we have by assumption an equivalence φ:V₁ ≃ₗ[k] V₂. We
-- choose a basis b₁ of V₁ and use Basis.map b₁ φ to form a basis for
-- V₂. The corresponding matrices will be the same (because of the
-- `compat` term in `equiv_of_spaces_with_form`.

-- to prove ←, we use the two bases to *build* a linear equivalence V₁
-- ≃ₗ[k] V₂. We must use the condition on the matrices to provide the
-- `compat` term in `equiv_of_spaces_with_form`.

theorem equiv_via_matrices  {ι:Type} [Fintype ι] [DecidableEq ι] 
  (β₁:BilinForm k V₁)   (β₂:BilinForm k V₂)
  : Nonempty (equiv_of_spaces_with_form β₁ β₂) ↔  ∃ b₁:Basis ι k V₁, ∃ b₂:Basis ι k V₂, 
    (BilinForm.toMatrix b₁ β₁) =  (BilinForm.toMatrix b₂ β₂)
  := by sorry
