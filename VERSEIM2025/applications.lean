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
  (M : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) k)
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

theorem det_of_block_matrix  [FiniteDimensional k V] {ι₁ ι₂ : Type} [Fintype  ι₁] [Fintype ι₂] (M: Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) k)
  (bm: Matrix.IsBlockDiagonal M) {Mblock : Matrix.BlockDiagonal M} [DecidableEq ι₁] [DecidableEq ι₂]
  {h : Mblock = extractBlockDiagonal M bm}: M.det = (Mblock.A).det * (Mblock.B).det := by
  unfold Matrix.det
  rw[h]
  unfold extractBlockDiagonal
  simp

  sorry

theorem Submodule.finrank_sup_eq_neg_finrank_inf_add {u v : Type} {K : Type u} {V : Type v} [DivisionRing K] [AddCommGroup V] [Module K V]
  (s t : Submodule K V) [FiniteDimensional K ↥s] [FiniteDimensional K ↥t] :
  Module.finrank K ↥(s ⊔ t) = Module.finrank K ↥s + Module.finrank K ↥t - (Module.finrank K ↥(s ⊓ t)) := by
    rw[Nat.sub_eq_of_eq_add']
    rw[← Submodule.finrank_sup_add_finrank_inf_eq]
    rw[add_comm]

#check LinearMap.BilinForm.finrank_orthogonal
#check  Submodule.finrank_sup_add_finrank_inf_eq

theorem ortho_complement_nondeg (β:BilinForm k V) [FiniteDimensional k V]
  (bnd : BilinForm.Nondegenerate β)
  (W W₁ :Submodule k V) (h : W₁ = BilinForm.orthogonal β W) (wnd : Nondeg_subspace β W) (href : β.IsRefl)
  [DecidableEq ↑(Basis.ofVectorSpaceIndex k ↥(W₁))]
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
        let Wplus := W ⊔ β.orthogonal W
        have k₁₀ : Wplus = W ⊔ β.orthogonal W := by
            rfl
        have k₁₁ : Module.finrank k (Wplus) = Module.finrank k V := by
          rw[k₁₀]
          rw[Submodule.finrank_sup_eq_neg_finrank_inf_add]
          rw[h] at k₀
          rw[k₀]
          simp
          rw[LinearMap.BilinForm.finrank_orthogonal]
          · rw[← add_comm]
            refine Nat.sub_add_cancel ?_
            apply Submodule.finrank_le
          · exact bnd
          · exact href
          · exact V
          · exact k
        apply Submodule.eq_top_of_finrank_eq at k₁₁
        rw[← k₁₀]
        rw[k₁₁]
        simp
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
        unfold b₁
        unfold b₂




       /-  refine BilinForm.isOrtho_def.mp ?_
        have k₂₀ : (b₂ j) ∈ (⊤:Submodule k W₁) := by
          exact trivial
        have k₂₁ : (b₁ i) ∈ (⊤:Submodule k W) := by
          exact trivial
        rw[LinearMap.BilinForm.mem_orthogonal_iff] at k₂₀
        -- apply this above theorem to k₂₀ -/
        sorry
      · intro i j
        rw[h] at b₂
        rw[h] at i
        unfold M
        simp

        -- i'm not sure if this is the right "direction" to be headed in
        --refine BilinForm.isOrtho_def.mp ?_
        /- unfold B
        unfold basis_of_direct_sum
        simp -/

        sorry
    let Mdiag := extractBlockDiagonal M k₂
    let M₁ := Mdiag.A
    let M₂ := Mdiag.B
    have k₃ : M.det = M₁.det * M₂.det := by
      exact det_of_block_matrix M k₂
    have k₄ : M₂ = (BilinForm.toMatrix b₂ (β.restrict W₁)) := by
      ext x₀ y₀
      unfold M₂
      unfold Mdiag
      unfold extractBlockDiagonal
      unfold M
      simp
      refine DFunLike.congr ?_ ?_
      · unfold B
        unfold basis_of_direct_sum
        simp
      · unfold B
        unfold basis_of_direct_sum
        simp
    have k₅ : M₂.det ≠ 0 := by
      intro h
      rw[h] at k₃
      rw[mul_zero] at k₃
      have k₅₀ : M.det ≠ 0 := by
        exact (BilinForm.nondegenerate_iff_det_ne_zero B).mp bnd
      exact k₅₀ k₃
    unfold Nondeg_subspace
    rw[k₄] at k₅
    apply Matrix.nondegenerate_of_det_ne_zero at k₅
    exact (BilinForm.nondegenerate_toMatrix_iff b₂).mp k₅
