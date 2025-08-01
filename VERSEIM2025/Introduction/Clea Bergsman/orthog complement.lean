--------------------------------------------------------------------------------
/-
Copyright (c) 2025 Clea Bergsman, Katherine Buesing, George McNinch, Sahan Wijetunga. All rights reserved.

Released under the Apache 2.0 license as described in the file LICENSE.

VERSEIM-2025 REU VERSEIM-2025 REU @ Tufts University 
-/

import Mathlib.Tactic
import VERSEIM2025.BilinearForms
import VERSEIM2025.Subspaces

-- Katherine and Clea, I think you can prove various things using the
-- "basis of internal direct sum" theorem that Katherine finished
-- proving.

-- suppose that (V,β) is a space with a non-degenerate bilinear from
-- and that W is a subspace of V

open LinearMap (BilinForm)
open LinearMap

variable {k V:Type} [Field k] [AddCommGroup V] [Module k V]
variable {β:BilinForm k V}
variable {ι₁ ι₂ : Type} [DecidableEq ι₁] [DecidableEq ι₂]

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



def zero_mat : Matrix ι₁ ι₂ k := fun _ _ => (0 : k)

def Matrix.IsBlockDiagonal (M : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) k) : Prop :=
  (∀ i j, M (Sum.inl i) (Sum.inr j) = 0) ∧
  (∀ i j, M (Sum.inr i) (Sum.inl j) = 0)

structure Matrix.BlockDiagonal (M : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) k) where
  A : Matrix ι₁ ι₁ k
  B : Matrix ι₂ ι₂ k
  eq : M = Matrix.fromBlocks A zero_mat zero_mat B

def extractBlockDiagonal
  {M : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) k}
  (h : Matrix.IsBlockDiagonal M) : Matrix.BlockDiagonal M :=
  {
    A := λ i j => M (Sum.inl i) (Sum.inl j),
    B := λ i j => M (Sum.inr i) (Sum.inr j),
    eq := by
      ext i j
      cases i with
      | inl i' =>
        cases j with
        | inl j' => rfl
        | inr j' => exact h.1 i' j'
      | inr i' =>
        cases j with
        | inl j' => exact h.2 i' j'
        | inr j' => rfl
  }


theorem ortho_complement_nondeg  [FiniteDimensional k V] (bnd : BilinForm.Nondegenerate β)
  (W W₁ :Submodule k V) (h : W₁ = BilinForm.orthogonal β W) (wnd : Nondeg_subspace β W) [ DecidableEq ↑(Basis.ofVectorSpaceIndex k ↥(W₁))]
  [DecidableEq ↑(Basis.ofVectorSpaceIndex k ↥W)]:
  Nondeg_subspace β W₁ := by
    have k₀ : W ⊔ W₁ = ⊤ := by
      rw[h]
      rw[IsCompl.sup_eq_top]
      exact BilinearForms.isCompl_orthogonal_of_restrict_nondegenerate β W wnd
    have k₁ : W ⊓ W₁ = ⊥ := by
      rw[h]
      rw[IsCompl.inf_eq_bot]
      exact BilinearForms.isCompl_orthogonal_of_restrict_nondegenerate β W wnd
    let b₁ : Basis (Basis.ofVectorSpaceIndex k W) k W := Basis.ofVectorSpace k W
    let b₂ : Basis (Basis.ofVectorSpaceIndex k W₁) k W₁ := Basis.ofVectorSpace k W₁
    let B : Basis ((Basis.ofVectorSpaceIndex k W) ⊕ (Basis.ofVectorSpaceIndex k W₁)) k V := by
      apply basis_of_direct_sum
      · exact b₁
      · exact b₂
      · exact k₀
      · exact k₁
    let M : Matrix ((Basis.ofVectorSpaceIndex k W) ⊕ (Basis.ofVectorSpaceIndex k W₁)) ((Basis.ofVectorSpaceIndex k W) ⊕ (Basis.ofVectorSpaceIndex k W₁)) k := BilinForm.toMatrix B β
    have k₂ : Matrix.IsBlockDiagonal M := by
      unfold Matrix.IsBlockDiagonal
      constructor
      · intro b₃ b₄
        unfold M
        simp
        sorry
      · sorry
    let Mdiag := extractBlockDiagonal k\_2 
    let M₁ := Mdiag.A 
    let M₂ := Mdiag.B 
    
    have k₃ : M.det = M₁.det * M₂.det := by
      sorry
    -- i need to make a linear map for beta i think SOB
    have k₄ : M₂ = (BilinForm.toMatrix b₂ β) := by
      sorry
    sorry