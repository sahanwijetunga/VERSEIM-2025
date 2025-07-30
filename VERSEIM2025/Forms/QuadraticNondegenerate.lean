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
import VERSEIM2025.Forms.ReflexiveBilinearForms

namespace QuadraticForm

open scoped Polynomial
open scoped TensorProduct
open scoped PolynomialModule


variable {R M: Type*} [CommRing R] [AddCommGroup M] [Module R M]

def rad (Q: QuadraticForm R M): Submodule R M := radForm Q.polarBilin

theorem rad_iff (Q: QuadraticForm R M) (x: M): x ∈ Q.rad ↔ ∀ y, Q.polarBilin x y = 0 := by
  simp[rad,radForm]

theorem rad_iff' (Q: QuadraticForm R M) (x: M): x ∈ Q.rad ↔ ∀ y, Q.polarBilin y x = 0 := by
  simp[rad,radForm,QuadraticMap.polar]
  constructor; repeat
    intro h
    intro y
    rw[<- h y, add_comm]
    abel_nf

theorem in_rad_apply (Q: QuadraticForm R M) {x: M} (hx: x ∈ Q.rad) (y: M): Q.polarBilin x y = 0 := by
  exact (rad_iff Q x).mp hx y

theorem in_rad_apply' (Q: QuadraticForm R M) {x: M} (hx: x ∈ Q.rad) (y: M): Q.polarBilin y x= 0:= by
  exact (rad_iff' Q x).mp hx y

theorem in_rad_apply'' (Q: QuadraticForm R M) {x: M} (hx: x ∈ Q.rad) (y: M): Q (x+y) = Q y := sorry

theorem in_rad_apply''' (Q: QuadraticForm R M) {x: M} (hx: x ∈ Q.rad) (y: M): Q (y+x) = Q y := sorry

noncomputable def quotient_rad (Q: QuadraticForm R M): QuadraticForm R (M ⧸ Q.rad) where
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
    simp
    sorry
  exists_companion' := sorry

theorem quotient_rad_polarBilin (Q: QuadraticForm R M): Q.quotient_rad.polarBilin=  quot_form (B := Q.polarBilin) sorry := by
  simp[quotient_rad]
  sorry


theorem quotient_rad_nondegenerate (Q: QuadraticForm R M): LinearMap.BilinForm.Nondegenerate Q.quotient_rad.polarBilin := by
  rw[quotient_rad_polarBilin]
  exact reflexive_quotient_radForm_nondegenerate _ _

theorem range_quotient_rad_eq_range (Q: QuadraticForm R M): Set.range Q.quotient_rad = Set.range Q := sorry

theorem range_baseChange_quotient_rad_eq_range_baseChange [Invertible (2:R)] (A: Type*) [CommRing A] [Algebra R A]
  (Q: QuadraticForm R M): Set.range (Q.baseChange A) = Set.range (Q.quotient_rad.baseChange A) :=
  sorry



end QuadraticForm
