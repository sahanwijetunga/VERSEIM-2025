
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.BilinearMap

open LinearMap
open LinearMap (BilinForm)
open Module

variable {k V V₁ V₂ :Type} [Field k]
  [AddCommGroup V] [Module k V]
  [AddCommGroup V₁] [Module k V₁]
  [AddCommGroup V₂] [Module k V₂]


structure isometry
  (β₁:BilinForm k V₁)
  (β₂:BilinForm k V₂)
  where
    equiv : V₁ ≃ₗ[k] V₂
    compat : ∀ (v w : V₁), (β₁ v) w = (β₂ (equiv  v)) (equiv w)


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

lemma equiv_from_bases_apply (b₁:Basis ι k V₁) (b₂:Basis ι k V₂)  :
  ∀ i:ι, (equiv_from_bases b₁ b₂) (b₁ i) = b₂ i := by
  unfold equiv_from_bases
  intro i
  rw [ LinearEquiv.trans_apply ]
  rw [ Basis.repr_self ]
  rw [ Basis.repr_symm_apply ]
  rw [ Finsupp.linearCombination_single ]
  apply one_smul

theorem equiv_via_matrices  {ι:Type} [Fintype ι] [DecidableEq ι]
  (β₁:BilinForm k V₁)   (β₂:BilinForm k V₂) (b₁ : Basis ι k V₁) 
  : Nonempty (isometry β₁ β₂) ↔  ∃ b₂:Basis ι k V₂, ∀ i j : ι,
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
  apply isometry.mk
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

--------------------------------------------------------------------------------

notation:100 lhs:100 "≃[" field:100 "," lhb:100 "," rhb:100 "]" rhs:100 =>
  isometry (k:= field) (V₁ := lhs) (V₂ := rhs) lhb rhb


def anisotropicVector {V : Type} [ AddCommGroup V ] [ Module k V ]
  (β:BilinForm k V) (v:V) : Prop := β v v ≠ 0

def anisotropic {V : Type} [ AddCommGroup V ] [ Module k V ]
  (β:BilinForm k V) : Prop := ∀ v, v ≠ 0 → anisotropicVector β v


theorem anisotropic_of_equiv (eq : V₁ ≃[k,β₁,β₂] V₂) (han : anisotropic β₂)
  : anisotropic β₁ := by
  intro v hᵥ
  unfold anisotropicVector
  have h₁ : (β₂ (eq.equiv v)) (eq.equiv v) ≠ 0 := by
    apply han;
    exact (LinearEquiv.map_ne_zero_iff eq.equiv).mpr hᵥ
  have h₂ : (β₁ v) v = (β₂ (eq.equiv v)) (eq.equiv v) := by apply eq.compat
  rw [← h₂] at h₁
  exact h₁

example (β:BilinForm k V₁) : β.IsSymm := by
  intro v w

theorem symm_of_equiv {β₁:BilinForm k V₁} {β₂:BilinForm k V₂}
  (eq : V₁ ≃[k,β₁,β₂] V₂) (hsymm : β₂.IsSymm)
  : β₁.IsSymm := by
  rw [ BilinForm.isSymm_def]
  intro v w
  have β₂_symm : (β₂ (eq.equiv v)) (eq.equiv w) = (β₂ (eq.equiv w)) (eq.equiv v) := by 
    apply hsymm v w
  have h₁ : (β₁ v) w = (β₂ (eq.equiv v)) (eq.equiv w) := by apply eq.compat
  have h₂ : (β₁ v) w = (β₂ (eq.equiv w)) (eq.equiv v) := by rw [β₂_symm] at h₁; exact h₁
  have h₃ : (β₁ w) v = (β₂ (eq.equiv w)) (eq.equiv v) := by apply eq.compat
  rw [← h₂] at h₃
  simp
  symm
  exact h₃

theorem alt_of_equiv (eq : V₁ ≃[k,β₁,β₂] V₂) (halt : β₂.IsAlt)
  : β₁.IsAlt := by
  intro v
  have β₂_alt : (β₂ (eq.equiv v)) (eq.equiv v) = 0 := by apply halt
  have h₁ : (β₁ v) v = (β₂ (eq.equiv v)) (eq.equiv v) := by apply eq.compat
  rw [β₂_alt] at h₁
  exact h₁

theorem nondeg_of_equiv (eq : V₁ ≃[k,β₁,β₂] V₂) (hnd : β₂.Nondegenerate)
  : β₁.Nondegenerate := by
  intro v h₁
  have h₂ : (∀ (w : V₂), (β₂ (eq.equiv v)) w = 0) → (eq.equiv v) = 0 := by
    exact hnd (eq.equiv v)
  have h₃ : ∀ (n:V₁), (β₁ v) n = (β₂ (eq.equiv v)) (eq.equiv n) := by
    apply eq.compat
  have eq₁ : eq.equiv v = 0 → v = 0 := by
    intro h
    exact (LinearEquiv.map_eq_zero_iff eq.equiv).mp h
  apply eq₁
  apply h₂
  intro w
  let x : V₁ := eq.equiv.invFun w
  have h₅ : eq.equiv x = w := by exact (LinearEquiv.eq_symm_apply eq.equiv).mp rfl
  rw [← h₅]
  have h₄ : ∀ (n : V₁), (β₂ (eq.equiv v)) (eq.equiv n) = 0 := by
    intro n
    rw [← h₃]
    apply h₁
  apply h₄

def isometry.symm {β₁:BilinForm k V₁} {β₂:BilinForm k V₂}
  (e:V₁ ≃[k,β₁,β₂] V₂) :
  V₂ ≃[k,β₂,β₁] V₁ where
    equiv := e.equiv.symm
    compat := by
      intro y z
      let v : V₁ := e.equiv.invFun y
      let w : V₁ := e.equiv.invFun z
      have h₁ : (β₁ v) w = (β₂ (e.equiv v)) (e.equiv w) := by
        apply e.compat
      have hv : e.equiv v = y := by exact (LinearEquiv.eq_symm_apply e.equiv).mp rfl
      have hw : e.equiv w = z := by exact (LinearEquiv.eq_symm_apply e.equiv).mp rfl
      rw [hv, hw] at h₁
      have hy : v = e.equiv.invFun y := by rfl
      have hz : w = e.equiv.invFun z := by rfl
      rw [hy, hz] at h₁
      simp at h₁
      symm at h₁
      exact h₁

def isometry.symmetric {β₁:BilinForm k V₁} {β₂:BilinForm k V₂}
  (e:V₁ ≃[k,β₁,β₂] V₂) : --(v w : V₁) (y z : V₂) :
  V₂ ≃[k,β₂,β₁] V₁ := by
  apply isometry.mk
  intro y z
  let v : V₁ := e.equiv.invFun y
  let w : V₁ := e.equiv.invFun z
  have h₁ : (β₁ v) w = (β₂ (e.equiv v)) (e.equiv w) := by
    apply e.compat
  have hv : e.equiv v = y := by exact (LinearEquiv.eq_symm_apply e.equiv).mp rfl
  have hw : e.equiv w = z := by exact (LinearEquiv.eq_symm_apply e.equiv).mp rfl
  rw [hv, hw] at h₁
  have hy : v = e.equiv.invFun y := by rfl
  have hz : w = e.equiv.invFun z := by rfl
  rw [hy, hz] at h₁
  simp at h₁
  symm at h₁
  swap
  have eq : V₂ ≃ₗ[k] V₁ := e.equiv.symm
  exact eq
  simp
  exact h₁

variable  {V₃ :Type}
  [AddCommGroup V₃] [Module k V₃]

def isometry.trans  {β₁:BilinForm k V₁} {β₂:BilinForm k V₂}
  {β₃:BilinForm k V₃} (e₁:V₁ ≃[k,β₁,β₂] V₂) (e₂:V₂ ≃[k,β₂,β₃] V₃) :
  V₁ ≃[k,β₁,β₃] V₃ where
    equiv := e₁.equiv.trans e₂.equiv
    compat := by
      intro x y
      have h₁ : (β₁ x) y = (β₂ (e₁.equiv x)) (e₁.equiv y) := by
        apply e₁.compat
      have h₂ : (β₂ (e₁.equiv x)) (e₁.equiv y) = (β₃ (e₂.equiv (e₁.equiv x))) (e₂.equiv (e₁.equiv y)) := by
        apply e₂.compat
      rw [h₂] at h₁
      simp
      exact h₁

def isometry.transitive  {β₁:BilinForm k V₁} {β₂:BilinForm k V₂}
  {β₃:BilinForm k V₃} (e₁:V₁ ≃[k,β₁,β₂] V₂) (e₂:V₂ ≃[k,β₂,β₃] V₃) :
  V₁ ≃[k,β₁,β₃] V₃ := by
  apply isometry.mk
  intro x y
  have h₁ : (β₁ x) y = (β₂ (e₁.equiv x)) (e₁.equiv y) := by
    apply e₁.compat
  have h₂ : (β₂ (e₁.equiv x)) (e₁.equiv y) = (β₃ (e₂.equiv (e₁.equiv x))) (e₂.equiv (e₁.equiv y)) := by
    apply e₂.compat
  rw [h₂] at h₁
  swap
  have e₃ : V₁ ≃ₗ[k] V₃ := e₁.equiv.trans e₂.equiv
  exact e₃
  simp
  exact h₁
