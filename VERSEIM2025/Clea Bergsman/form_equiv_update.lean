import Mathlib.Tactic

open Module
open LinearMap
open LinearMap (BilinForm)


variable  {k V₁ V₂ :Type} [Field k]
  [AddCommGroup V₁] [Module k V₁]
  [AddCommGroup V₂] [Module k V₂]

structure equiv_of_spaces_with_form
  (β₁:BilinForm k V₁)
  (β₂:BilinForm k V₂)
  where
    equiv : V₁ ≃ₗ[k] V₂
    compat : ∀ (x y : V₁), β₁ x y = β₂ (equiv x) (equiv y)


notation:100 lhs:100 "≃[" field:100 "," lhb:100 "," rhb:100 "]" rhs:100 =>
  equiv_of_spaces_with_form (k:= field) (V₁ := lhs) (V₂ := rhs) lhb rhb


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

theorem symm_of_equiv (eq : V₁ ≃[k,β₁,β₂] V₂) (hsymm : β₂.IsSymm)
  : β₁.IsSymm := by
  intro v w
  have β₂_symm : (β₂ (eq.equiv v)) (eq.equiv w) = (β₂ (eq.equiv w)) (eq.equiv v) := by apply hsymm
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

def equiv_of_spaces_with_form.symm {β₁:BilinForm k V₁} {β₂:BilinForm k V₂}
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

def equiv_of_spaces_with_form.symmetric {β₁:BilinForm k V₁} {β₂:BilinForm k V₂}
  (e:V₁ ≃[k,β₁,β₂] V₂) : --(v w : V₁) (y z : V₂) :
  V₂ ≃[k,β₂,β₁] V₁ := by
  apply equiv_of_spaces_with_form.mk
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

def equiv_of_spaces_with_form.trans  {β₁:BilinForm k V₁} {β₂:BilinForm k V₂}
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

def equiv_of_spaces_with_form.transitive  {β₁:BilinForm k V₁} {β₂:BilinForm k V₂}
  {β₃:BilinForm k V₃} (e₁:V₁ ≃[k,β₁,β₂] V₂) (e₂:V₂ ≃[k,β₂,β₃] V₃) :
  V₁ ≃[k,β₁,β₃] V₃ := by
  apply equiv_of_spaces_with_form.mk
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
