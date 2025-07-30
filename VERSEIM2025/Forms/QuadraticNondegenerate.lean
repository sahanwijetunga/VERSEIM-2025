--------------------------------------------------------------------------------
/-
Copyright (c) 2025 Clea Bergsman, Katherine Buesing, George McNinch, Sahan Wijetunga. All rights reserved.

Released under the Apache 2.0 license as described in the file LICENSE.

VERSEIM-2025 REU @ Tufts University
-/

import Mathlib.Tactic
import Mathlib.Algebra.Polynomial.Module.Basic
import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.LinearAlgebra.QuadraticForm.Isometry
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.Flat.Basic

import VERSEIM2025.PolynomialModuleDegree.Misc
import VERSEIM2025.Forms.RationalFunctionFields.PolynomialModule
import VERSEIM2025.Forms.Reflexive.Radical

namespace QuadraticForm

open scoped Polynomial
open scoped TensorProduct
open scoped PolynomialModule


variable {R M: Type*} [CommRing R] [AddCommGroup M] [Module R M]

def rad (Q: QuadraticForm R M): Submodule R M := radForm Q.polarBilin

theorem rad_iff (Q: QuadraticForm R M) (x: M): x ∈ Q.rad ↔ ∀ y, Q.polarBilin x y = 0 := by rfl

theorem rad_iff' (Q: QuadraticForm R M) (x: M): x ∈ Q.rad ↔ ∀ y, Q.polarBilin y x = 0 := by
  simp[rad,radForm,QuadraticMap.polar]
  constructor; repeat
    intro h
    intro y
    rw[<- h y, add_comm]
    abel_nf

@[simp]
theorem in_rad_apply (Q: QuadraticForm R M) {x: M} (hx: x ∈ Q.rad) (y: M): Q.polarBilin x y = 0 := by
  exact (rad_iff Q x).mp hx y

@[simp]
theorem in_rad_apply' (Q: QuadraticForm R M) {x: M} (hx: x ∈ Q.rad) (y: M): Q.polarBilin y x= 0:= by
  exact (rad_iff' Q x).mp hx y


theorem in_rad_apply'' (Q: QuadraticForm R M) {x: M} (hx: x ∈ Q.rad) (y: M) [Invertible (2:R)]: Q (x+y) = Q y := by
  rw[QuadraticMap.map_add Q x y]
  rw[<- QuadraticMap.polarBilin_apply_apply]
  rw[in_rad_apply Q hx y]
  simp
  suffices h:2 • (Q x) = 0 from ?_
  . have: 2 • (Q x) = (2:R) * Q x := by exact Eq.symm (ofNat_smul_eq_nsmul R 2 (Q x))
    rw[this] at h
    calc
      Q x = (1:R) * (Q x) := by rw[one_mul]
      _ = (⅟ (2: R) * (2: R)) * (Q x) := by
        rw [Invertible.invOf_mul_self]
      _ = ⅟ (2: R) * ((2: R) * Q x) := by
        rw[mul_assoc]
      _ = 0 := by
        rw[h, mul_zero]
  rw[<- QuadraticMap.polar_self]
  exact hx x

theorem in_rad_apply''' (Q: QuadraticForm R M) {x: M} (hx: x ∈ Q.rad) (y: M) [Invertible (2:R)]: Q (y+x) = Q y := by
  rw[add_comm]
  exact in_rad_apply'' Q hx y


theorem polarBilin_isSymm (Q: QuadraticForm R M): Q.polarBilin.IsSymm := by
  intro x y
  simp only [QuadraticMap.polarBilin_apply_apply, RingHom.id_apply]
  exact QuadraticMap.polar_comm (⇑Q) x y

example (a b c: M) (h: a-b=c): a=b+c := by
  exact Eq.symm (add_eq_of_eq_sub' (id (Eq.symm h)))

noncomputable def quotient_rad (Q: QuadraticForm R M) [Invertible (2:R)]: QuadraticForm R (M ⧸ Q.rad) where
  toFun := by
    apply Quotient.lift Q
    intro a b hab
    have contain: a-b ∈ Q.rad := by
      apply (Submodule.quotientRel_def (x := a) (y := b) (p := Q.rad)).mp
      exact hab
    have: a = a-b + b := by
      simp
    rw[this]
    exact in_rad_apply'' _ contain _
  toFun_smul := by
    intro a
    intro v
    induction' v using Submodule.Quotient.induction_on with v
    rw[<- Submodule.Quotient.mk_smul]
    simp[Submodule.Quotient.mk]
    rw[<- smul_eq_mul _ (Q v)]
    exact QuadraticMap.map_smul Q a v
  exists_companion' := by -- why does rewriting not work?
    use quot_form (B := Q.polarBilin) (LinearMap.BilinForm.IsSymm.isRefl Q.polarBilin_isSymm)
    intro x y
    induction' x using Submodule.Quotient.induction_on with x
    induction' y using Submodule.Quotient.induction_on with y
    rw[<- Submodule.Quotient.mk_add]
    simp[Submodule.Quotient.mk, QuadraticMap.polar, <- Submodule.Quotient.mk_add]
    have: quot_form (B := Q.polarBilin) (LinearMap.BilinForm.IsSymm.isRefl (polarBilin_isSymm Q))
      (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = Q.polarBilin x y := by
      exact quot_form_apply (B := Q.polarBilin) (LinearMap.BilinForm.IsSymm.isRefl (polarBilin_isSymm Q)) (v := x) (w := y)
    symm
    apply add_eq_of_eq_sub'
    rw[sub_add_eq_sub_sub]
    simpa [Submodule.Quotient.mk, QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar] using this

theorem quotient_rad_apply (Q: QuadraticForm R M) (x: M)[Invertible (2:R)]: Q.quotient_rad (Submodule.Quotient.mk  x) = Q x := rfl


theorem quotient_rad_polarBilin (Q: QuadraticForm R M)[Invertible (2:R)]: Q.quotient_rad.polarBilin =
  quot_form (B := Q.polarBilin) (LinearMap.BilinForm.IsSymm.isRefl Q.polarBilin_isSymm) := by
  ext x y
  simp[QuadraticMap.polar,quotient_rad_apply, <- Submodule.Quotient.mk_add]
  have: quot_form (B := Q.polarBilin) (LinearMap.BilinForm.IsSymm.isRefl (polarBilin_isSymm Q))
    (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = Q.polarBilin x y := quot_form_apply (B := Q.polarBilin) Q.polarBilin_isSymm.isRefl (v := x) (w := y)
  apply Eq.trans (h₂ := this.symm)
  simp[QuadraticMap.polar]


theorem quotient_rad_nondegenerate (Q: QuadraticForm R M)[Invertible (2:R)]: LinearMap.BilinForm.Nondegenerate Q.quotient_rad.polarBilin := by
  rw[quotient_rad_polarBilin]
  exact reflexive_quotient_radForm_nondegenerate _ _

-- this is amazing to me that rfl works! (finally lean working as I want it)
theorem quotient_rad_comp (Q: QuadraticForm R M)[Invertible (2:R)]: Q.quotient_rad.comp Q.rad.mkQ = Q := rfl

theorem range_comp_eq {N: Type*} [AddCommGroup N] [Module R N] (Q : QuadraticForm R M)
  (f : N →ₗ[R] M) (hf: Function.Surjective f):
  Set.range (Q.comp f) = Set.range Q := by
  ext x
  constructor
  . rintro ⟨y, rfl⟩
    exact Set.mem_range_self (f y)
  . rintro ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := hf y
    exact Set.mem_range_self z

theorem range_quotient_rad_eq_range (Q: QuadraticForm R M)[Invertible (2:R)]: Set.range Q.quotient_rad = Set.range Q := by
  rw[<- range_comp_eq Q.quotient_rad Q.rad.mkQ (Submodule.mkQ_surjective Q.rad)]
  rw[quotient_rad_comp]

theorem range_baseChange_quotient_rad_eq_range_baseChange [Invertible (2:R)] (A: Type*) [CommRing A] [Algebra R A]
  (Q: QuadraticForm R M): Set.range (Q.baseChange A) = Set.range (Q.quotient_rad.baseChange A) :=
  sorry



end QuadraticForm
