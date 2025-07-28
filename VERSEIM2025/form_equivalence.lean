
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.BilinearMap

open LinearMap
open LinearMap (BilinForm)
open BigOperators
open Module

variable {k V V₁ V₂ :Type} [Field k]
  [AddCommGroup V] [Module k V]
  [AddCommGroup V₁] [Module k V₁]
  [AddCommGroup V₂] [Module k V₂]

variable { Φ:V₁ ≃ₗ[k] V₂ }

-- given the linear equivalence φ, here is how to get a basis of V₂ from a basis of V₁

example {ι : Type} [Fintype ι] (b₁:Basis ι k V₁) ( φ:V₁ ≃ₗ[k] V₂ ):
  Basis ι k V₂ := b₁.map φ


/-- here is what it means for the pair (V₁,β₁) to be equivalent to (V₂,β₂) : -/
structure equiv_of_spaces_with_form
  (β₁:BilinForm k V₁)
  (β₂:BilinForm k V₂)
  where
    equiv : V₁ ≃ₗ[k] V₂
    compat : ∀ (v w : V₁), (β₁ v) w = (β₂ (equiv  v)) (equiv w)

notation:100 lhs:100 "≃[" field:100 "," lhb:100 "," rhb:100 "]" rhs:100 => 
  equiv_of_spaces_with_form (k:= field) (V₁ := lhs) (V₂ := rhs) lhb rhb

lemma equiv_of_series {ι:Type} [Fintype ι] (β:BilinForm k V) (b : Basis ι k V)
  (s t : ι → k)
  : (β (Fintype.linearCombination k ⇑b t)) (Fintype.linearCombination k ⇑b s) =
    ∑ i:ι, (∑ j:ι, (t i) * (s j) * (β (b i) (b j))) := by
  unfold Fintype.linearCombination
  dsimp
  rw [LinearMap.BilinForm.sum_left]
  apply Finset.sum_congr
  rfl
  intro i h
  rw [LinearMap.BilinForm.sum_right]
  apply Finset.sum_congr
  rfl
  intro j g
  rw [LinearMap.BilinForm.smul_left]
  rw [mul_comm]
  rw [LinearMap.BilinForm.smul_right]
  ring

lemma equiv_of_bilin_series {ι:Type} [Fintype ι] (β:BilinForm k V) (v w : ι → V)
  : (β (∑ i, v i)) (∑ j, w j) =
    ∑ i:ι, (∑ j:ι, (β (v i) (w j))) := by
  rw [LinearMap.BilinForm.sum_left]
  apply Finset.sum_congr
  rfl
  intro i h
  rw [LinearMap.BilinForm.sum_right]

def equiv_from_bases (b₁:Basis ι k V₁) (b₂:Basis ι k V₂)
  : V₁ ≃ₗ[k] V₂ :=
  LinearEquiv.trans b₁.repr (b₂.repr.symm)

lemma fintype_linear_combination_repr {ι:Type} [Fintype ι] (v:V) (b : Basis ι k V) :
  (Fintype.linearCombination k b) (b.repr v) = v := by
  apply Eq.trans _ (Basis.linearCombination_repr b v)
  rw [ Fintype.linearCombination_apply ]
  rw [ Finsupp.linearCombination_apply ]
  rw [ Finsupp.sum_fintype ]
  simp

lemma equiv_from_bases_apply (b₁:Basis ι k V₁) (b₂:Basis ι k V₂) (i:ι) :
  ∀ i:ι, (equiv_from_bases b₁ b₂) (b₁ i) = b₂ i := by
  unfold equiv_from_bases
  intro i
  rw [ LinearEquiv.trans_apply ]
  rw [ Basis.repr_self ]
  rw [ Basis.repr_symm_apply ]
  rw [ Finsupp.linearCombination_single ]
  apply one_smul

/-- The statement that (V₁,β₁) is equivalent to (V₂,β₂) if and only if
  there are bases b₁ the matrix of β₁ 
-/
theorem equiv_via_matrices  {ι:Type} [Fintype ι] [DecidableEq ι]
  (β₁:BilinForm k V₁)   (β₂:BilinForm k V₂) (b₁ : Basis ι k V₁) 
  : Nonempty (V₁ ≃[k,β₁,β₂]V₂) ↔  
    ∃ b₂:Basis ι k V₂, ∀ i j : ι,
    (BilinForm.toMatrix b₁ β₁) i j =  (BilinForm.toMatrix b₂ β₂) i j
  := by
  constructor
  -- mp
  intro ⟨N⟩
  let b₂ : Basis ι k V₂ := Basis.map b₁ N.equiv
  use b₂
  unfold b₂
  unfold BilinForm.toMatrix
  simp
  intro i j
  rw [N.compat (b₁ i) (b₁ j)]
  -- mpr
  intro h₁
  rcases h₁ with ⟨b₂, h₁⟩
  refine Nonempty.intro ?_
  let eq : V₁ ≃ₗ[k] V₂ := by apply equiv_from_bases; exact b₁; exact b₂
  have identify_bases : ∀ i:ι, b₂ i = eq (b₁ i) := by
    intro i; unfold eq;  rw [← equiv_from_bases_apply b₁ b₂ i]
  apply equiv_of_spaces_with_form.mk
  intro v w
  swap
  exact eq
  have sum_v : v = (Fintype.linearCombination k ⇑b₁) (b₁.repr v):=
    by symm; apply fintype_linear_combination_repr
  have sum_w : w = (Fintype.linearCombination k ⇑b₁) (b₁.repr w):=
    by symm; apply fintype_linear_combination_repr
  nth_rw 1 [sum_v, sum_w]
  rw [equiv_of_series]
  nth_rw 2 [sum_v, sum_w]
  rw [ Fintype.linearCombination_apply, Fintype.linearCombination_apply]
  rw [ map_sum eq, map_sum eq]
  rw [equiv_of_bilin_series]
  apply Finset.sum_congr
  rfl
  intro i hᵢ
  apply Finset.sum_congr
  rfl
  intro j hⱼ
  rw [map_smul eq, map_smul eq]
  rw [LinearMap.BilinForm.smul_left]
  rw [mul_comm]
  rw [LinearMap.BilinForm.smul_right]
  rw [mul_comm]
  rw [← identify_bases, ← identify_bases]
  rw [← BilinForm.toMatrix_apply b₁ β₁ i j,← BilinForm.toMatrix_apply b₂ β₂]
  rw [h₁ i j]
  ring

