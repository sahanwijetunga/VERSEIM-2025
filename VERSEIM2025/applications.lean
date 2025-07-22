import Mathlib.Tactic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

import VERSEIM2025.Subspaces
import VERSEIM2025.block

-- Katherine and Clea, I think you can prove various things using the
-- "basis of internal direct sum" theorem that Katherine finished
-- proving.

-- suppose that (V,β) is a space with a non-degenerate bilinear from
-- and that W is a subspace of V

open LinearMap (BilinForm)
open LinearMap

variable {k V:Type} [Field k] [AddCommGroup V] [Module k V]

variable {β:BilinForm k V}
variable {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]


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

def p (ι₁ ι₂ : Type) [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]: ι₁ ⊕ ι₂ → Prop := by
  intro i
  exact (∃ (y : ι₁), i = Sum.inl y)


/- theorem block_diag_is_triangular (i j : ι₁ ⊕ ι₂) (M : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) k)
 (h: M.IsBlockDiagonal) :  ∀ i, ¬(p ι₁ ι₂) i → ∀ j , (p ι₁ ι₂) j → M i j = 0 := by
  unfold Matrix.IsBlockDiagonal at h
  intro x h₁ y h₂
  unfold p at h₁
  unfold p at h₂
  simp at h₁

  sorry

#check DecidablePred
theorem det_of_block_matrix  [FiniteDimensional k V] {ι₁ ι₂ : Type} {I : ι₁ ⊕ ι₂} [Fintype  ι₁] [Fintype ι₂] (M: Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) k)
  (bm: Matrix.IsBlockDiagonal M) {Mblock : Matrix.BlockDiagonal M} [DecidableEq ι₁] [DecidableEq ι₂] [DecidablePred (p ι₁ ι₂)]
  {h : Mblock = extractBlockDiagonal M bm}: M.det = (Mblock.A).det * (Mblock.B).det := by
  have k₀: ∀ (i : ι₁ ⊕ ι₂), ¬(p ι₁ ι₂) i → ∀ (j : ι₁ ⊕ ι₂), (p ι₁ ι₂) j → M i j = 0 := by
    apply block_diag_is_triangular
    · trivial
    · trivial
    · exact bm
  rw[Matrix.twoBlockTriangular_det M (p ι₁ ι₂) k₀ ]
  unfold Matrix.toSquareBlockProp
  rw[h]
  unfold extractBlockDiagonal
  simp
  --apply Matrix.toBlock_apply
  #check Matrix.toBlock_apply

  /- M.det = (Matrix.toSquareBlockProp M p).det *
            (Matrix.toSquareBlockProp M (fun i => ¬ p i)).det :=
  Matrix.twoBlockTriangular_det M p h -/
  sorry
-/

theorem finrank_sup_eq_neg_finrank_inf_add {u v : Type} {K : Type u} {V : Type v} [DivisionRing K] [AddCommGroup V] [Module K V]
  (s t : Submodule K V) [FiniteDimensional K ↥s] [FiniteDimensional K ↥t] :
  Module.finrank K ↥(s ⊔ t) = Module.finrank K ↥s + Module.finrank K ↥t - (Module.finrank K ↥(s ⊓ t)) := by
    rw[Nat.sub_eq_of_eq_add']
    rw[← Submodule.finrank_sup_add_finrank_inf_eq]
    rw[add_comm]

lemma left_mem_basis_direct_sum {ι₁ ι₂ :Type}
              (W₁ W₂ : Submodule k V)
              (B₁ : Basis ι₁ k W₁)
              (B₂ : Basis ι₂ k W₂)
              [FiniteDimensional k V] [Fintype ι₁] [DecidableEq ι₁]
              [Fintype ι₂]  [DecidableEq ι₂]
        (hspan : W₁ ⊔ W₂ = (⊤: Submodule k V))
        (hindep : W₁ ⊓ W₂ = (⊥:Submodule k V)) (i:ι₁) :
        (basis_of_direct_sum W₁ W₂ B₁ B₂ hspan hindep) (Sum.inl i) ∈ W₁ := by
        unfold basis_of_direct_sum
        unfold Sum.elim
        simp

lemma right_mem_basis_direct_sum {ι₁ ι₂ :Type}
              (W₁ W₂ : Submodule k V)
              (B₁ : Basis ι₁ k W₁)
              (B₂ : Basis ι₂ k W₂)
              [FiniteDimensional k V] [Fintype ι₁] [DecidableEq ι₁]
              [Fintype ι₂]  [DecidableEq ι₂]
        (hspan : W₁ ⊔ W₂ = (⊤: Submodule k V))
        (hindep : W₁ ⊓ W₂ = (⊥:Submodule k V)) (i:ι₂) :
        (basis_of_direct_sum W₁ W₂ B₁ B₂ hspan hindep) (Sum.inr i) ∈ W₂ := by
        unfold basis_of_direct_sum
        unfold Sum.elim
        simp


theorem ortho_complement_nondeg (β:BilinForm k V) [FiniteDimensional k V]
  (bnd : BilinForm.Nondegenerate β)
  (W :Submodule k V) /- (h : W₁ = BilinForm.orthogonal β W) -/ (wnd : Nondeg_subspace β W) (href : β.IsRefl)
  [DecidableEq ↑(Basis.ofVectorSpaceIndex k ↥W)] [DecidableEq (BilinForm.orthogonal β W)]
  [DecidablePred (p ↑(Basis.ofVectorSpaceIndex k ↥W) ↑(Basis.ofVectorSpaceIndex k ↥(BilinForm.orthogonal β W)))]
  {brefl : LinearMap.BilinForm.IsRefl β }:
  Nondeg_subspace β (BilinForm.orthogonal β W) := by
    let ι₁ := (Basis.ofVectorSpaceIndex k ↥W)
    let ι₂ := (Basis.ofVectorSpaceIndex k ↥(BilinForm.orthogonal β W))
    have k₀ : W ⊓ (BilinForm.orthogonal β W) = ⊥ := by
      rw[IsCompl.inf_eq_bot]
      exact (BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal brefl).mp wnd
    have k₁ : W ⊔ (BilinForm.orthogonal β W) = ⊤ := by
      ext x
      constructor
      · simp
      · simp
        let Wplus := W ⊔ β.orthogonal W
        have k₁₀ : Wplus = W ⊔ β.orthogonal W := by
            rfl
        have k₁₁ : Module.finrank k (Wplus) = Module.finrank k V := by
          rw[k₁₀]
          rw[finrank_sup_eq_neg_finrank_inf_add]
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
    let b₁ : Basis ι₁ k W := Basis.ofVectorSpace k W
    let b₂ : Basis ι₂ k (BilinForm.orthogonal β W) := Basis.ofVectorSpace k (BilinForm.orthogonal β W)
    let B : Basis (ι₁ ⊕ ι₂) k V := by
      apply basis_of_direct_sum
      · exact b₁
      · exact b₂
      · exact k₁
      · exact k₀
    let M : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) k := BilinForm.toMatrix B β
    let M₁ := Matrix.submatrix M Sum.inl Sum.inl
    let M₂ := Matrix.submatrix M Sum.inr Sum.inr
    let Mdiag := Matrix.fromBlocks M₁ 0 0 M₂
    /- have j₂ : M = Mdiag := by
      unfold M Mdiag
      ext x y
      simp
      unfold B Matrix.fromBlocks
      sorry -/
    /- have k₂ : M.BlockTriangular (p (Basis.ofVectorSpaceIndex k ↥W) (Basis.ofVectorSpaceIndex k ↑(BilinForm.orthogonal β W))) := by
      --unfold Matrix.BlockTriangular

      ---apply Matrix.upper_two_blockTriangular M₁ 0 M₂ g
      intro x y g

      unfold M



      sorry -/
    have g : ∀ i, ¬(p ι₁ ι₂) i → ∀ j , (p ι₁ ι₂) j → M i j = 0 := by
      intro x j₀ y j₁
      unfold p at j₀
      unfold p at j₁
      unfold M
      have g₀ : B x ∈ W := by
        --simp at j₀


        sorry
      have g₁ : ∀ i, ¬ (p ι₁ ι₂) i → B i ∈ (BilinForm.orthogonal β W) := by
        sorry
      --rw[g₀] at j₁

      sorry


    have k₃ : M.det = M₁.det * M₂.det := by
      rw[Matrix.twoBlockTriangular_det M (p (Basis.ofVectorSpaceIndex k ↥W) (Basis.ofVectorSpaceIndex k (BilinForm.orthogonal β W))) g]
      apply Mathlib.Tactic.LinearCombination'.mul_pf
      ·
        unfold M₁
        unfold p
        rw[Matrix.toSquareBlockProp_def]
        unfold Matrix.submatrix
        unfold Matrix.of
        unfold M
        simp

        sorry
      ·
        sorry


    have k₄ : M₂ = (BilinForm.toMatrix b₂ (β.restrict (BilinForm.orthogonal β W))) := by
      ext x₀ y₀
      unfold M₂ M
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
