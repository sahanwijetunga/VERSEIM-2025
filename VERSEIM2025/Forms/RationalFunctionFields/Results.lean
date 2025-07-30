--------------------------------------------------------------------------------
/-
Copyright (c) 2025 Clea Bergsman, Katherine Buesing, George McNinch, Sahan Wijetunga. All rights reserved.

Released under the Apache 2.0 license as described in the file LICENSE.

VERSEIM-2025 REU @ Tufts University
-/

import VERSEIM2025.Forms.RationalFunctionFields.CasselsPfister
import Mathlib.LinearAlgebra.TensorProduct.Pi

namespace RationalFunctionFields

open scoped Polynomial
open scoped TensorProduct
open scoped PolynomialModule
open CasselsPfister

variable {F R: Type*} [Field F] [CommRing R]

#check QuadraticMap.weightedSumSquares
#check QuadraticMap.weightedSumSquares_apply

def standard_quadratic_form (n: ℕ): QuadraticForm R (Fin n → R) :=
    QuadraticMap.weightedSumSquares R (fun (_: Fin n) => (1:R))

theorem standard_quadratic_form_apply (n: ℕ) (f: Fin n → R):
    standard_quadratic_form n f = ∑ i, f i * f i := by
    rw[standard_quadratic_form, QuadraticMap.weightedSumSquares_apply]
    simp

noncomputable def equiv_tensor {A I: Type*} [Fintype I] [DecidableEq I] [CommRing A] [Algebra F A]:
 A ⊗[F] (I → F) ≃ₗ[A] I → A :=  TensorProduct.piScalarRight F A A I

theorem extend_standard_quadratic_form {A: Type*} [CommRing A] [Algebra F A] (n: ℕ)
[Invertible (2:F)]: QuadraticMap.comp (standard_quadratic_form (R := A) n)
(equiv_tensor (I := Fin n) (F := F) (A := A)) = (standard_quadratic_form (R := F) n).baseChange A := by
    unfold equiv_tensor
    unfold standard_quadratic_form
    refine QuadraticMap.ext_iff.mpr ?_
    intro x
    sorry

theorem sum_squares (f: F[X]) [Invertible (2:F)] {n: ℕ} {l: Fin n → F(X)} (hlf: f = ∑ i, l i * l i):
    ∃ l': Fin n → F[X], f = ∑ i, l' i * l' i := by
    let φ: QuadraticForm F (Fin n → F) := standard_quadratic_form (R := F) n
    have:  (f: F(X) ) ∈ Set.range (φ.baseChange F(X) ) := by
        use (equiv_tensor (I := Fin n)).invFun l
        rw[<- extend_standard_quadratic_form n]
        simp[standard_quadratic_form_apply n l, hlf]
    have: f ∈ Set.range (φ.baseChange F[X]) := by
        rw[<- range_quadratic_polynomial_eq_restrict_rational φ]
        exact this
    obtain ⟨v, hv⟩ := this
    rw[<- extend_standard_quadratic_form, QuadraticMap.comp_apply,
        LinearEquiv.coe_coe, standard_quadratic_form_apply] at hv
    use (equiv_tensor (I := Fin n)) v
    exact hv.symm



end RationalFunctionFields
