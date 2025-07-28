
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.BilinearMap

open LinearMap
open LinearMap (BilinForm)
open BigOperators

variable {k V V₁ V₂ :Type} [Field k]
  [AddCommGroup V] [Module k V]
  [AddCommGroup V₁] [Module k V₁]
  [AddCommGroup V₂] [Module k V₂]

variable { Φ:V₁ ≃ₗ[k] V₂ }

-- given the linear equivalence φ, here is how to get a basis of V₂ from a basis of V₁

example {ι : Type} [Fintype ι] (b₁:Basis ι k V₁) ( φ:V₁ ≃ₗ[k] V₂ ):
  Basis ι k V₂ := b₁.map φ


-- here is what it means for the pair (V₁,β₁) to be equivalent to
-- (V₂,β₂) :

structure equiv_of_spaces_with_form
  (β₁:BilinForm k V₁)
  (β₂:BilinForm k V₂)
  where
    equiv : V₁ ≃ₗ[k] V₂
    compat : ∀ (v w : V₁), (β₁ v) w = (β₂ (equiv  v)) (equiv w)

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

  --apply (MulLECancellable.inj (t i) ((β (b i)) (s j • b j)) (s j * (β (b i)) (b j))).mpr
  --rw [Fintype.sum_congr (by trivial) h₁]

  --rw [← h₂, ← h₁]
  --unfold Finsupp.linearCombination
  --dsimp
  --have h₁ (i :ι) : (β (∑ i:ι, (t i) • (b i))) (∑ j:ι, (s j) • (b j)) =
   -- ∑ i:ι, ((β ((t i) • (b i))) (∑ j:ι, (s j) • (b j)))
   -- := by rw [LinearMap.BilinForm.sum_left]
 -- have h₂ (i : ι) : ((β ((t i) • (b i))) (∑ j:ι, (s j) • (b j))) =
  --  ∑ j:ι, (β ((t i) • (b i))) ((s j) • (b j))
  --  := by
   --   rw [LinearMap.BilinForm.sum_right]
  --have h₃ (i j : ι ): (β (t i • b i)) (s j • b j) = (t i) * (β (b i)) (s j • b j)
  --  := by rw [LinearMap.BilinForm.smul_left]
  --have h₄ (i j : ι ): (β (b i)) (s j • b j) = (s j) * (β (b i) (b j))
  --  := by rw [LinearMap.BilinForm.smul_right]



#check LinearMap.BilinForm.sum_right
#check LinearMap.BilinForm.smul_left
#check LinearMap.BilinForm.smul_right
#check Finset.sum_congr
#check MulLECancellable.inj

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

theorem equiv_via_matrices  {ι:Type} [Fintype ι] [DecidableEq ι]
  (β₁:BilinForm k V₁)   (β₂:BilinForm k V₂) (b₁ : Basis ι k V₁) (i j : ι) (s t : ι → k)
  : Nonempty (equiv_of_spaces_with_form β₁ β₂) ↔  ∃ b₂:Basis ι k V₂, ∀ i j : ι,
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

  --apply (mul_left_cancel_iff _ _ _ (((b₁.repr v) i) * (b₁.repr w) j) ((β₁ (b₁ i)) (b₁ j)) ((β₂ (eq (b₁ i))) (eq (b₁ j)))).mp







#check Basis.sum_equivFun
#check Basis.linearCombination_repr
#check LinearMap.BilinForm.ext_basis
#check Finsupp.linearCombination_onFinset
#check LinearMap.BilinForm.congr_apply
#check Equiv.congr_fun
#check LinearMap.congr_fun₂
#check LinearMap.ext_iff₂
#check Finsupp.finset_sum_apply
#check Finset.sum_apply'
#check Basis.map_apply
#check map_smul



#check toMatrix₂
#check BilinForm.toMatrix_apply
#check LinearMap.BilinForm.ext_basis
#check Basis.ext
#check Module.Free.constr
#check toMatrix_apply

-- (toMatrix b₁ β₁) i j = β₁ (b₁ i) (b₂ j)
-- toMatrix b₂ β₂) i j = β₂ (N.equiv (b₁ i)) (N.equiv (b₁ j))
--unfold Fintype.linearCombination
 -- simp
 -- apply Finset.sum_congr
 -- rfl
 -- intro x h₂
 -- rw [Finset.mul_sum]
 -- apply Finset.sum_congr
 -- rfl
  --intro y h₃
 -- rw [← identify_bases, ← identify_bases, mul_comm]

  --have h₄ : (β₁ (b₁ x)) (b₁ y) = (β₂ (b₂ y)) (b₂ x) := by rw [h₁]
  --rw [← Basis.map_apply, ← Basis.map_apply]



  --rw [mul_assoc ((b₁.repr v) i) ((b₁.repr w) j) ((β₁ (b₁ i)) (b₁ j))]
  --apply (LinearMap.ext_iff₂ β₁ β₂).mpr
  --have sum_v : v = (Finsupp.linearCombination k ⇑b₁) (b₁.repr v) := by symm; apply Basis.linearCombination_repr b₁ v
  --have sum_w : w = (Finsupp.linearCombination k ⇑b₁) (b₁.repr w) := by symm; apply Basis.linearCombination_repr b₁ w
