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
import VERSEIM2025.PolynomialModuleDegree.Misc

/- Partially duplicates material from `Basics` for easier use in
CasselsPfisterTheorem -/

namespace HyperbolicTwoSpace

open scoped Polynomial
open scoped TensorProduct
open scoped PolynomialModule

variable {F V: Type*} [Field F] [AddCommGroup V] [Module F V]

/-- A pair `e`,`f` is Hyperbolic.

Stated assuming `R` is only a commutative ring to allow use of `F[X]`-/
def hyp_pair {R M: Type*} [CommRing R] [AddCommGroup M] [Module R M]  (β:LinearMap.BilinForm R M) (e f : M) : Prop :=
  β e e = 0  ∧  β f f = 0  ∧  β e f = 1

/-- A hyperbolic pair for the polar form of a quadratic form satisfies nice properties. -/
theorem QuadraticFormNice  {R M: Type*} [CommRing R] [AddCommGroup M] [Module R M]
 {φ: QuadraticForm R M} {e f : M} (h: hyp_pair φ.polarBilin e f) [Invertible (2:R)]:
  φ e = 0 ∧ φ f = 0 ∧ QuadraticMap.polar φ e f = 1 ∧ φ (e+f)=1 := by
  have ⟨h1,h2,h3⟩ := h
  have h1: 2*φ e = 0 := by simpa using h1
  have h2: 2*φ f = 0 := by simpa using h2
  have h' {e: M} (he: 2*φ e = 0): φ e = 0 := by
    calc
      φ e = (1: R) * φ e := one_mul (φ e)|> .symm
      _ = (⅟2 * 2) * φ e := by simp
      _ = ⅟2 * (2 * φ e) := by rw[mul_assoc]
      _ = ⅟2 * 0 := by rw[he]
      _ = 0 := by simp
  constructor
  . exact h' h1
  constructor
  . exact h' h2
  constructor
  . simpa using h3
  rw[QuadraticMap.map_add φ e f, h' h1, h' h2]
  simpa using h3


protected lemma exists_bilin_one {e: V} {B: LinearMap.BilinForm F V} (enz: e ≠ 0)
  (hn: LinearMap.BilinForm.Nondegenerate B): ∃f, B e f =1 := by
    have: ∃ f, B e f ≠ 0 := by
      contrapose! enz
      exact hn e enz
    have ⟨f, hf⟩ := this
    let a := B e f
    use a⁻¹ • f
    calc
      (B e) (a⁻¹ • f) = a⁻¹ * (B e f) := by simp only [map_smul, smul_eq_mul]
      _ = a⁻¹ * a := rfl
      _ = 1 := inv_mul_cancel₀ hf


theorem Exists {e: V} {β:LinearMap.BilinForm F V} (bsymm : β.IsSymm)
  (hn: LinearMap.BilinForm.Nondegenerate β) (enz : e ≠ 0) (eiso : β e e  = 0) [Invertible (2:F)]:
  ∃ f, hyp_pair β e f := by
    have ⟨v, hv⟩ := HyperbolicTwoSpace.exists_bilin_one enz hn
    let c := - 2⁻¹ * β v v
    let v' := v+c • e
    use v'
    constructor
    . exact eiso
    constructor
    . unfold v' c
      have : β v e = 1 := by
        rw[<- bsymm]
        exact hv
      field_simp[*]
      ring
    . unfold v' c
      simp_all

/-- Given `φ: V → F` has a hyperbolic pair, `φ: V[X] → F[X]` does as well (via the inclusion `V → V[X]`)-/
theorem Extend {φ: QuadraticForm F V}[Invertible (2:F)] {e f: V} (h: hyp_pair φ.polarBilin e f):
  ∃ e' f', hyp_pair (φ.baseChange F[X]).polarBilin e' f' := by
  use 1 ⊗ₜ e
  use 1 ⊗ₜ f
  have he: φ e = 0 := by
      have: (2:F) ≠ 0 := by
        exact two_ne_zero
      have := h.1
      simp_all[h.1,QuadraticMap.polarBilin]
  have hf: φ f = 0 := by
      have: (2:F) ≠ 0 := by
        exact two_ne_zero
      have := h.2.1
      simp_all[h.2.1,QuadraticMap.polarBilin]

  constructor
  . simp[he]
  constructor
  . simp[hf]
  . have: 1 ⊗ₜ[F] e + 1 ⊗ₜ[F] f = (1 ⊗ₜ (e+f): F[X] ⊗[F] V) := by
      exact Eq.symm (TensorProduct.tmul_add 1 e f)
    have hef:= h.2.2
    simp_all[QuadraticMap.polar,QuadraticMap.polarBilin,this]

/-- If `M` has a hyperbolic pair `e`, `f` then `Set.range φ = Set.univ`.

Stated only assuming `R` is a commutative ring so it works over `F[X]`-/
theorem QuadraticForm_Entire
{R M: Type*} [CommRing R] [AddCommGroup M] [Module R M]  (φ: QuadraticForm R M) {e f: M}
  (hef: hyp_pair φ.polarBilin e f) [Invertible (2:R)]:
  Set.range φ = Set.univ := by
  ext x
  constructor; intro h; trivial
  intro _
  use x• e+f
  calc
    φ (x • e + f) = φ (x • e)+φ f + QuadraticMap.polar φ (x • e) f := by
      exact QuadraticMap.map_add (⇑φ) (x • e) f
    _ = (x*x) • φ e+φ f + x*QuadraticMap.polar φ e f := by
      rw [@QuadraticMap.polar_smul_left]
      rw [@QuadraticMap.map_smul]
      rfl
    _ = x := by
      have ⟨h1,h2,h3,h4⟩  := QuadraticFormNice hef
      rw[h1,h2,h3]
      simp

end HyperbolicTwoSpace
