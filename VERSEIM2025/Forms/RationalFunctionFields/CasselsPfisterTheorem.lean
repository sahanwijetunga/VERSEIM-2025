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

namespace CasselsPfister

open scoped Polynomial
-- open scoped QuadraticForm
open scoped RatFunc
open scoped TensorProduct

variable {F V: Type} [Field F] [AddCommGroup V] [Module F V] [Invertible (2: F)]

example:= PolynomialModule F V
example:= F[X] ⊗[F] V


theorem FooSumWork {α}(v w: α →₀ V) (g : α → V →+ V):
  (v+w).sum (fun a => fun v => g a v) = (v.sum (fun a => fun v => g a v)) + (w.sum (fun a => fun v => g a v)) := by
    exact Finsupp.sum_hom_add_index g

-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/TensorProduct/MvPolynomial.html#MvPolynomial.rTensor
--  is relevant (but does things in multivariable polynomials)
noncomputable def PolynomialEquiv: PolynomialModule F V ≃ₗ[F[X]] F[X] ⊗[F] V := sorry


/-- The degree of a polynomial v : V[X] -/
def PolynomialModule_degree (v: PolynomialModule F V): WithBot ℕ :=  v.support.max

/-- The degree defined in `PolynomialModule_degree` agrees with Polynomial notion of degree.-/
example (p: F[X]): p.degree = p.support.max := rfl

/-- Ports over degree notion from `PolynomialModule_degree` via `PolynomialEquiv` isomorphism. -/
noncomputable abbrev TensorPolynomialModule_degree (v: F[X] ⊗[F] V):
  WithBot ℕ :=PolynomialModule_degree (PolynomialEquiv.invFun v)

/-- Constant polynomial a: F in F[X]-/
noncomputable example (a: F): F[X] := Polynomial.C a

def HyperplaneReflection {φ: QuadraticForm F V} {v: V} (hv: φ v ≠ 0):   QuadraticMap.Isometry φ φ where
  toFun := fun w ↦ w-((QuadraticMap.polar φ v w ) * (φ v )⁻¹) • v
  map_add' := by
    intro w1 w2
    rw[QuadraticMap.polar_add_right φ v w1 w2]
    module
  map_smul' := by
    intro c w
    rw[QuadraticMap.polar_smul_right φ]
    dsimp only [smul_eq_mul, RingHom.id_apply]
    module
  map_app' := by
    intro w
    calc
     φ (w - (QuadraticMap.polar φ v w * (φ v)⁻¹) • v) =
      φ w + φ (-(QuadraticMap.polar φ v w * (φ v)⁻¹) • v) + QuadraticMap.polar φ w (-(QuadraticMap.polar (φ) v w * (φ v)⁻¹) • v)
      := by
      rw[sub_eq_add_neg]
      rw[QuadraticMap.map_add φ]
      simp
    _ = φ w + (QuadraticMap.polar φ v w)^2  * (φ v)⁻¹ + - (QuadraticMap.polar φ v w)^2  * (φ v)⁻¹  := by
      have h1: φ (-(QuadraticMap.polar φ v w * (φ v)⁻¹) • v) = (QuadraticMap.polar φ v w)^2  * (φ v)⁻¹ := by
        rw[QuadraticMap.map_smul,pow_two]
        field_simp
        ring
      have h2: QuadraticMap.polar φ w (-(QuadraticMap.polar (φ) v w * (φ v)⁻¹) • v) = -(QuadraticMap.polar φ v w)^2  * (φ v)⁻¹ := by
        rw[pow_two,QuadraticMap.polar_comm]
        field_simp
      rw[h1,h2]
    _ = φ w := by
      simp

/-- TODO: Formalize construction of τ_w(r),f'-/
protected lemma GetSmallerDegree (f: F[X]) (u r: PolynomialModule F V)
  (hf: f.degree > 0): True := sorry

noncomputable example (Q: QuadraticForm F V) [Invertible (2: F)]:
  QuadraticForm F[X] (F[X] ⊗[F] V) := QuadraticForm.baseChange F[X] Q

noncomputable example (Q: QuadraticForm F V) [Invertible (2: F)]:
  QuadraticForm (RatFunc F) ((RatFunc F) ⊗[F] V) := QuadraticForm.baseChange (RatFunc F)  Q











/-- The values taken by the extension of a quadratic map φ: V → F to V(X) → F(X)
    that are within F[X] are taken by the extension V[X] → F[X] as well.
-/
theorem CasselsPfister (φ: QuadraticForm F V): (algebraMap F[X] (RatFunc F))⁻¹' (Set.range (φ.baseChange (RatFunc F)))
   = Set.range (φ.baseChange F[X])  := sorry



end CasselsPfister
