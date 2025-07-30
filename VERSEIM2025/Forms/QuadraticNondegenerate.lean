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


variable {R M: Type*} [CommRing R] [AddCommGroup M] [Module R M] [Invertible (2:R)]

def rad (Q: QuadraticForm R M): Submodule R M := radForm Q.associated

theorem rad_iff (Q: QuadraticForm R M) (x: M): x ∈ Q.rad ↔ ∀ y, Q.associated x y = 0 := sorry
theorem rad_iff' (Q: QuadraticForm R M) (x: M): x ∈ Q.rad ↔ ∀ y, Q.associated y x = 0 := sorry

theorem rad_apply (Q: QuadraticForm R M) {x: M} (hx: x ∈ Q.rad) (y: M): Q (x+y) = Q y := sorry

noncomputable def quotient_rad (Q: QuadraticForm R M): QuadraticForm R (M ⧸ Q.rad) := sorry

theorem quotient_rad_nondegenerate (Q: QuadraticForm R M): LinearMap.BilinForm.Nondegenerate Q.quotient_rad.polarBilin := sorry

theorem range_quotient_rad_eq_range (Q: QuadraticForm R M): Set.range Q.quotient_rad = Set.range Q := sorry

theorem range_baseChange_quotient_rad_eq_range_baseChange (A: Type*) [CommRing A] [Algebra R A]
  (Q: QuadraticForm R M): Set.range (Q.baseChange A) = Set.range (Q.quotient_rad.baseChange A) :=
  sorry



end QuadraticForm
