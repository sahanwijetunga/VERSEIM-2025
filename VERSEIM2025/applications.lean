import Mathlib.Tactic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

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

/- theorem is_block_diagonal_iff_block_diag (M :  Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) k)
(h: ) -/

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

/- theorem det_of_block_matrix  [FiniteDimensional k V] (ι₁ ι₂: Type) (M: Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) k)
  (bm: Matrix.IsBlockDiagonal M) {Mblock : extractBlockDiagonal bm} : M.extractBlockDiagonal.det = (Mblock.A).det * (Mblock.B).det := by
    sorry -/

#check LinearMap.BilinForm.finrank_orthogonal
theorem ortho_complement_nondeg  (β:BilinForm k V) [FiniteDimensional k V]
  (bnd : BilinForm.Nondegenerate β)
  (W W₁ :Submodule k V) (h : W₁ = BilinForm.orthogonal β W) (wnd : Nondeg_subspace β W)
  [ DecidableEq ↑(Basis.ofVectorSpaceIndex k ↥(W₁))]
  [DecidableEq ↑(Basis.ofVectorSpaceIndex k ↥W)] [DecidableEq (BilinForm.orthogonal β W)]
  {brefl : LinearMap.BilinForm.IsRefl β }:
  Nondeg_subspace β W₁ := by
    have k₀ : W ⊓ W₁ = ⊥ := by
      rw[h]
      rw[IsCompl.inf_eq_bot]
      exact (BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal brefl).mp wnd
    have k₁ : W ⊔ W₁ = ⊤ := by
      rw[h]
      ext x
      constructor
      · simp
      · simp
        /- intro s h
        simp at h -/

        have k₁₀ : Module.finrank k (⊤ : Submodule (W ⊔ β.orthogonal W)) = Module.finrank k V := by
          sorry
        sorry
      /- rw[IsCompl.sup_eq_top]
      refine IsCompl.symm (IsCompl.symm ?_) -/
      --rw[LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint]
      --rw[LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal]
      /- · exact wnd
      · sorry -/
            /- rw[← LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal]
      · exact wnd
      · sorry -/
    let b₁ : Basis (Basis.ofVectorSpaceIndex k W) k W := Basis.ofVectorSpace k W
    let b₂ : Basis (Basis.ofVectorSpaceIndex k W₁) k W₁ := Basis.ofVectorSpace k W₁
    let B : Basis ((Basis.ofVectorSpaceIndex k W) ⊕ (Basis.ofVectorSpaceIndex k W₁)) k V := by
      apply basis_of_direct_sum
      · exact b₁
      · exact b₂
      · exact k₁
      · exact k₀
    let M : Matrix ((Basis.ofVectorSpaceIndex k W) ⊕ (Basis.ofVectorSpaceIndex k W₁)) ((Basis.ofVectorSpaceIndex k W) ⊕ (Basis.ofVectorSpaceIndex k W₁)) k := BilinForm.toMatrix B β
    have k₂ : Matrix.IsBlockDiagonal M := by
      unfold Matrix.IsBlockDiagonal
      constructor
      · intro i j
        unfold M
        simp
        unfold B
        unfold basis_of_direct_sum
        simp
        refine mem_ker.mp ?_

        /- refine BilinForm.isOrtho_def.mp ?_
        have k₂₀ : (b₂ j) ∈ (⊤:Submodule k β) := by
          exact trivial
        have k₂₁ : (b₁ i) ∈ (⊤:Submodule k W) := by
          exact trivial
        apply LinearMap.BilinForm.mem_orthogonal_iff at k₂₀
        -- apply this above theorem to k₂₀ -/
        sorry
      · intro b₃ b₄
        unfold M
        simp
        -- i'm not sure if this is the right "direction" to be headed in
        refine BilinForm.isOrtho_def.mp ?_
        rw[h] at b₃
        unfold B
        unfold basis_of_direct_sum
        simp
        rw[h] at b₂

        sorry
    let Mdiag := extractBlockDiagonal k₂
    let M₁ := Mdiag.A
    let M₂ := Mdiag.B
    have k₃ : M.det = M₁.det * M₂.det := by
    -- we may want to create a separate theorem or lemma for this
      sorry
    have k₄ : M₂ = (BilinForm.toMatrix b₂ (β.restrict W₁)) := by
      ext x₀ y₀
      unfold M₂
      unfold Mdiag
      unfold extractBlockDiagonal
      unfold M
      simp
      refine DFunLike.congr ?_ ?_
      ·
        refine LinearMap.congr_arg ?_

        sorry
      ·
        sorry
    have k₅ : M₂.det ≠ 0 := by
      intro h
      rw[h] at k₃
      rw[mul_zero] at k₃
      -- i need to have a theorem that says M.det doesnt equal zero so that I can get a contradiction
      -- why do we know it's not zero again?? ?
      sorry
    unfold Nondeg_subspace
    rw[k₄] at k₅
    apply Matrix.nondegenerate_of_det_ne_zero at k₅
    exact (BilinForm.nondegenerate_toMatrix_iff b₂).mp k₅
