import Mathlib.Tactic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

-- Katherine and Clea, I think you can prove various things using the
-- "basis of internal direct sum" theorem that Katherine finished
-- proving.

-- suppose that (V,β) is a space with a non-degenerate bilinear from
-- and that W is a subspace of V

open LinearMap (BilinForm)
open LinearMap

variable {k V:Type} [Field k] [AddCommGroup V] [Module k V]

variable {β:BilinForm k V}

-- let's make a precidicate for subspaces on which the form is
-- non-degenerate (I think Sahan must have some version of this, but I
-- looked in his code and in mathlib and didn't see exactly what I
-- wanted...)

def Nondeg_subspace (β : BilinForm k V) (W:Submodule k V) : Prop :=
  BilinForm.Nondegenerate (BilinForm.restrict β W)

-- we want to prove: if W is a non-degenerate subspace, then also its
-- orthogonal complement is non-degenerate

-- I think previously I had given a def/construction for orthogonal
-- complement, but it is actually already in Mathlib, as
-- `LinearMap.BilinForm.orthogonal`


/- need to figure out how to state that we have a basis for W and W orth.compl -/
theorem ortho_complement_nondeg (bnd : BilinForm.Nondegenerate β)
  (W:Submodule k V) (wnd : Nondeg_subspace β W) :
  Nondeg_subspace β (BilinForm.orthogonal β W) := by
    have k₀ : (BilinForm.orthogonal β W) ⊔ W = ⊤ := by
      sorry
    have k₁ : (BilinForm.orthogonal β W) ⊓ W = ⊥ := by
      sorry
    --have b : Basis ((Fintype (Module.finrank k W) ) ⊕ (Fintype (Module.finrank k (BilinForm.orthogonal β W))) k V


    -- have h₀ :
    /- need to get thr above have statement working, type errors  -/
    sorry
