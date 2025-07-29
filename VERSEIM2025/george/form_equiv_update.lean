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
    compat : ∀ (x y : V₁), β₁ x y = β₂ (equiv v₁) (equiv v₂) 

notation:100 lhs:100 "≃[" field:100 "," lhb:100 "," rhb:100 "]" rhs:100 => 
  equiv_of_spaces_with_form (k:= field) (V₁ := lhs) (V₂ := rhs) lhb rhb


def anisotropicVector {V : Type} [ AddCommGroup V ] [ Module k V ] 
  (β:BilinForm k V) (v:V) : Prop := β v v ≠ 0

def anisotropic {V : Type} [ AddCommGroup V ] [ Module k V ] 
  (β:BilinForm k V) : Prop := ∀ v, v ≠ 0 → anisotropicVector β v


theorem anisotropic_of_equiv (eq : V₁ ≃[k,β₁,β₂] V₂) (han : anisotropic β₁) : anisotropic β₂ := by sorry

theorem symm_of_equiv (eq : V₁ ≃[k,β₁,β₂] V₂) (hsymm : β₁.IsSymm) : β₂.IsSymm := by sorry

theorem alt_of_equiv (eq : V₁ ≃[k,β₁,β₂] V₂) (halt : β₁.IsAlt) : β₂.IsAlt := by sorry

theorem nondeg_of_equiv (eq : V₁ ≃[k,β₁,β₂] V₂) (hnd : β₁.Nondegenerate) : β₂.Nondegenerate := by sorry


--two more results!

def equiv_of_spaces_with_form.symm {β₁:BilinForm k V₁} {β₂:BilinForm k V₂} 
  (e:V₁ ≃[k,β₁,β₂] V₂) :
  V₂ ≃[k,β₂,β₁] V₁ = by sorry
