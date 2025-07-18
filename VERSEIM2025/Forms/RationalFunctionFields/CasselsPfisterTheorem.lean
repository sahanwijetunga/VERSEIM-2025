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

namespace CasselsPfister

open scoped Polynomial
open scoped TensorProduct
open scoped PolynomialModule


scoped[CasselsPfister] notation:10000 F "(X)" => RatFunc F
scoped[CasselsPfister] notation:100 V "[" F:100 "]" => F[X] ⊗[F] V
scoped[CasselsPfister] notation:100 V "(" F:100 ")"  => F(X) ⊗[F] V

variable {F V: Type*} [Field F] [AddCommGroup V] [Module F V]

example:= PolynomialModule F V -- V[X]
example:= V[F] -- Another way to express V[X] (which is not definitionally equal)

example:= V(F) -- F(X) ⊗ V, e.g. V(X)

theorem ConversionIff (a b: F[X]): (a: F(X))=b ↔ a=b := by
  constructor
  . intro h
    apply IsFractionRing.coe_inj.mp h
  . intro h
    rw[h]

theorem ExtensionScalarsCommutesWithScalars (p: F[X]) (v: V(F)) : p • v = (p: F(X)) • v := by
  sorry

theorem PolynomialScalarSmul (c: F) (u: F[X]): (Polynomial.C c) * u = c • u := by
  sorry

theorem TensorPolynomialScalarSmul (c: F) (u: V[F]): (Polynomial.C c) • u = c • u := by
  sorry

theorem RatFunc_coePolynomialMultiplication (f g: F[X]): (f*g: F[X]) = (f: F(X))*(g: F(X)) := by
  sorry

theorem RatFunc_coePolynomialScalarMultiplication (f: F[X]) (g: F(X)): ↑f * g = f • g:= by
  rw [@Algebra.smul_def',@mul_eq_mul_right_iff]; left
  rfl

/-- Maps `V[X] → V(X)` in the sense of extension by scalars using tensor products-/
noncomputable def toRatFuncTensor: V[F] →ₗ[F[X]] V(F) :=
  TensorProduct.AlgebraTensorModule.map (Algebra.linearMap F[X] (F(X))) LinearMap.id

noncomputable scoped instance : Coe (V[F]) (V(F)) := ⟨toRatFuncTensor⟩

/-- The map `toRatFuncTensor` is injective. -/
theorem toRatFuncTensor_Injective : Function.Injective (@toRatFuncTensor F V _ _ _):= sorry

/-- The map `toRatFuncTensor` commutes with polynomial scalar multiplication -/
theorem toRatFuncTensor_CommutePolynomialScalars (p: F[X]) (v: (V[F])):
  ((p • v): V(F)) = p • (v: V(F)) := sorry

/-- The map `toRatFuncTensor` commutes with scalar multiplication. -/
theorem toRatFuncTensor_CommuteScalars (a: F) (v: (V[F])):
  ((a • v): V(F)) = a • (v: V(F)) := sorry

/-- The map `toRatFuncTensor` commutes with quadratic forms. -/
theorem toRatFuncTensor_CommuteQuadraticForm (φ: QuadraticForm F V) (v: (V[F])) [Invertible (2:F)]:
  φ.baseChange F[X] v = (φ.baseChange F(X)) v := sorry



/-- The map `toRatFuncTensor` is injective, stated elementwise as an iff. -/
theorem toRatFuncTensor_Injective' (a b: V[F] ) : (a: V(F)) = b ↔ a=b := by
  have := @toRatFuncTensor_Injective F V _ _ _
  exact Function.Injective.eq_iff this

theorem FooSumWork {α}(v w: α →₀ V) (g : α → V →+ V):
  (v+w).sum (fun a => fun v => g a v) = (v.sum (fun a => fun v => g a v)) + (w.sum (fun a => fun v => g a v)) := by
    exact Finsupp.sum_hom_add_index g

@[simp]
noncomputable def FooFunPolynomial: ℕ → V →ₗ[F] V[F] := fun n => {
  toFun := fun v =>  (Polynomial.monomial n 1) ⊗ₜ v
  map_add' := fun a b => TensorProduct.tmul_add ((Polynomial.monomial n) 1) a b
  map_smul' := fun c a => TensorProduct.tmul_smul c ((Polynomial.monomial n) 1) a
}

-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/BigOperators/Finsupp/Basic.html#Finsupp.sum_hom_add_index
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Finsupp/LSum.html#Finsupp.sum_smul_index_linearMap'

-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/TensorProduct/MvPolynomial.html#MvPolynomial.rTensor
--  is relevant (but does things in multivariable polynomials)

/-- An isomorphism between the two notions of `V[X]`-/
noncomputable def PolynomialEquiv: PolynomialModule F V ≃ₗ[F[X]] V[F] where
  toFun := fun f => f.sum (fun n => fun v => FooFunPolynomial n v)
  map_add' := sorry
  map_smul' := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

noncomputable scoped instance : Coe (PolynomialModule F V) (V[F]) := ⟨PolynomialEquiv⟩

theorem PolynomialEquivSingle (v: V): (PolynomialModule.single F 0) v = (1 ⊗ₜ v: V[F]) := by
  simp only [PolynomialEquiv,FooFunPolynomial,DFunLike.coe,
    EquivLike.coe,PolynomialModule.single,Finsupp.singleAddHom, Mathlib.Tactic.Module.NF.eval,]
  rw[Finsupp.sum ]
  by_cases h:v=0
  . rw[h]
    simp
  . rw [Finsupp.support_single_ne_zero 0 h]
    simp

theorem FooSummWork {α}(v w: α →₀ V) (g : α → V →+ V):
  (v+w).sum (fun a => fun v => g a v) = (v.sum (fun a => fun v => g a v)) + (w.sum (fun a => fun v => g a v)) := by
    exact Finsupp.sum_hom_add_index g

/-- Reflects vectors across v.-/
def HyperplaneReflection (φ: QuadraticForm F V) (v: V) : QuadraticMap.Isometry φ φ where
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
        by_cases h: φ v = 0
        . rw[h]
          simp
        . field_simp
          ring
      have h2: QuadraticMap.polar φ w (-(QuadraticMap.polar (φ) v w * (φ v)⁻¹) • v) = -(QuadraticMap.polar φ v w)^2  * (φ v)⁻¹ := by
        rw[pow_two,QuadraticMap.polar_comm]
        field_simp
      rw[h1,h2]
    _ = φ w := by
      simp


theorem HyperplaneReflection_form (φ: QuadraticForm F V) (v: V) (w: V) (u: V) (huvw: w=v-u):
  HyperplaneReflection φ w v = u + ((φ w)⁻¹ * (φ u - φ v)) • w := sorry

      -- simp only [HyperplaneReflection,QuadraticMap.Isometry.instFunLike]
      -- simp only [LinearMap.coe_mk, AddHom.coe_mk]
      -- simp only [w]

/-- `in_polynomial_module v` means that `v` in `V(X)`is in `V[X]`.

  Implementation: `∃ (w : PolynomialModule F V), v = ↑w`
-/
def in_polynomial_module (v: V(F)): Prop :=
  ∃ (w : PolynomialModule F V), v = w

theorem in_polynomial_module_add {v w: V(F)} (hv: in_polynomial_module v)
  (hw: in_polynomial_module w): in_polynomial_module (v+w) := by
  obtain ⟨v', hv⟩ := hv
  obtain ⟨w', hw⟩ := hw
  use v'+w'
  dsimp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe]
  rw[map_add,hv,hw]
  simp

theorem in_polynomial_module_smul {v: V(F)} (p: F[X]) (hv: in_polynomial_module v):
   in_polynomial_module (p • v) := by
  obtain ⟨v', hv⟩ := hv
  use p • v'
  dsimp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe]
  rw[map_smul,hv]
  simp

/-- Each `v` in `V(X)` has non-zero `f: F[X]` with `f • v` in `V[X]`-/
theorem exists_denominator  (v: V(F)): ∃ (f: F[X]), in_polynomial_module (f • v) ∧ f ≠ 0 := by
  apply TensorProduct.induction_on (
    motive := fun v => ∃ f, in_polynomial_module (f • v) ∧ f ≠ 0
  )
  case zero =>
    use Polynomial.C 1
    constructor
    . use 0
      simp only [map_one, map_zero]
      rfl
    . intro h
      rw[map_one] at h
      exact one_ne_zero h
  case tmul =>
    intro f v
    use f.denom
    constructor
    . use f.num • (PolynomialModule.single F 0 v)
      simp only [AddHom.toFun_eq_coe,
        LinearMap.coe_toAddHom, map_smul, LinearEquiv.coe_coe]
      rw[PolynomialEquivSingle, ExtensionScalarsCommutesWithScalars]
      have: ↑f.denom • f ⊗ₜ[F] v  = (↑f.denom • f) ⊗ₜ[F] v  := by
        exact rfl
      simp only [toRatFuncTensor, TensorProduct.AlgebraTensorModule.map_tmul,
        Algebra.linearMap_apply, map_one, LinearMap.id_coe, id_eq]
      rw[TensorProduct.smul_tmul' ]
      rw[TensorProduct.smul_tmul' ]
      rw[<- RatFunc_coePolynomialScalarMultiplication]
      have : (((↑f.denom): F(X)) * f) = (↑f.num * 1)  := by
        rw[mul_one]
        have := RatFunc.num_div_denom f
        symm
        rw[mul_comm, <- div_eq_iff ]
        . exact this
        . intro h
          apply RatFunc.denom_ne_zero f
          have:  (f.denom: F(X)) = (0: F[X]) := by
            rw[h]
            simp[RatFunc.coePolynomial]
          exact (ConversionIff f.denom 0).mp this
      rw[<- this]
      rfl
    . exact RatFunc.denom_ne_zero f

  case add =>
    intro v w ⟨f, hfv⟩ ⟨g, hgw⟩
    use f*g
    constructor
    . have: (f * g) • (v + w) = f • g • v + f • g • w := by
        rw[ExtensionScalarsCommutesWithScalars, smul_add]
        repeat rw[ExtensionScalarsCommutesWithScalars]
        repeat rw[smul_smul]
        congr
        repeat exact RatFunc_coePolynomialMultiplication f g
      rw[this]
      apply in_polynomial_module_add
      . rw[smul_comm]
        apply in_polynomial_module_smul
        exact hfv.1
      . apply in_polynomial_module_smul
        exact hgw.1
    . exact (mul_ne_zero_iff_right hgw.2 ).mpr hfv.2



/-- `isGoodPair p φ v f` means `f • v` in `V[X]` and `φ(v)=p`-/
structure isGoodPair (p: F[X]) (φ: QuadraticForm F V) (v: V(F))(f: F[X]) [Invertible (2: F)]: Prop where
  prod_poly: in_polynomial_module (f • v)
  matches_image : (φ.baseChange (F(X))) v = p
  nonzero: f ≠ 0

/-- The set of `(v,f)` in `V(X) × F[X]` with `isGoodPair p φ v f`, i.e.
- `f • v ∈ V[X]`
- `φ(v)=p`
-/
def CollectionPairs (p: F[X]) (φ: QuadraticForm F V) [Invertible (2: F)]: Set ((V(F)) × F[X]) :=
  { (v,f) | isGoodPair p φ v f }


/-- There exists `(v,f)` in `V(X) × F[X]` with `(v,f)` satisfying `isGoodPair p φ v f`,
i.e. `f • v` in `V[X]` and `φ(v)=p`.

Stated as the set of such pairs nonempty for convenience.
-/
theorem NonemptyCollectionPairs (φ: QuadraticForm F V) [Invertible (2: F)] (p: F[X]) (hp:
  p ∈ (algebraMap F[X] (F(X)))⁻¹' (Set.range (φ.baseChange (F(X))))): (CollectionPairs p φ).Nonempty
   := by
  simp only [Set.mem_preimage, Set.mem_range] at hp
  obtain ⟨v, hv⟩ := hp
  obtain ⟨f, prod_poly, nonzero⟩ := exists_denominator v
  use (v,f)
  constructor
  . exact prod_poly
  . rw[hv]
    rfl
  . exact nonzero

@[simp]
def degree_pair: ((V(F)) × F[X]) → ℕ := fun (_,f) => f.natDegree

/-- Picks `(v,f)` in `V(X) × F[X]` such that `f.natDegree` is minimized with `(v,f)` satisfying
`isGoodPair p φ v f`, i.e. `f • v` in `V[X]` and `φ(v)=p`.

See `OptimalPair_isGoodPair` and `OptimalPair_isOptimal` for witnesses to this.
-/
noncomputable def OptimalPair (φ: QuadraticForm F V) [Invertible (2: F)] (p: F[X]) (hp:
  p ∈ (algebraMap F[X] (F(X)))⁻¹' (Set.range (φ.baseChange (F(X))))):
  (V(F)) × F[X] := Function.argminOn degree_pair (CollectionPairs p φ) (NonemptyCollectionPairs φ p hp)

/-- The `OptimalPair` is in the `CollectionPairs` set (i.e. is a good pair) -/
def OptimalPair_inCollectionPairs (φ: QuadraticForm F V) [Invertible (2: F)] (p: F[X]) (hp:
  p ∈ (algebraMap F[X] (F(X)))⁻¹' (Set.range (φ.baseChange (F(X))))):
  OptimalPair φ p hp ∈ (CollectionPairs p φ) := Function.argminOn_mem degree_pair (CollectionPairs p φ) (NonemptyCollectionPairs φ p hp)

/-- The `OptimalPair` is a good pair -/
def OptimalPair_isGoodPair (φ: QuadraticForm F V) [Invertible (2: F)] (p: F[X]) (hp:
  p ∈ (algebraMap F[X] (F(X)))⁻¹' (Set.range (φ.baseChange (F(X))))):
  isGoodPair p φ (OptimalPair φ p hp).1 (OptimalPair φ p hp).2 := OptimalPair_inCollectionPairs φ p hp

/-- The `OptimalPair` has optimal degree -/
def OptimalPair_isOptimal (φ: QuadraticForm F V) [Invertible (2: F)] (p: F[X]) (hp:
  p ∈ (algebraMap F[X] (F(X)))⁻¹' (Set.range (φ.baseChange (F(X)))))
  (f: F[X]) (v: V(F))  (hGoodPair: isGoodPair p φ v f)
  : ¬ f.natDegree< (OptimalPair φ p hp).2.natDegree := by
  suffices ¬ degree_pair (v,f) < degree_pair (OptimalPair φ p hp) from ?_
  . exact this
  apply Function.not_lt_argminOn
  exact hGoodPair


/-- Given `f: F[X]` with `f.natDegree=0` and `v:  V(F)` such that `isGoodPair p φ v f` we have
    `p ∈ Set.range (φ.baseChange F[X])`
-/
def in_BaseChangePolynomialModule_of_isGoodPair_constant (p: F[X]) (φ: QuadraticForm F V) (v: V(F))
(f: F[X]) (hf: f.natDegree=0) [Invertible (2: F)] (hGoodPair: isGoodPair p φ v f)
: p ∈ Set.range (φ.baseChange F[X]) := by
  rw[Polynomial.natDegree_eq_zero] at hf
  obtain ⟨a, haf⟩ := hf
  obtain ⟨prod_poly, matches_image, fnonzero⟩ := hGoodPair
  have anonzero: a ≠ 0 := by
    intro h
    rw[h] at haf
    simp at haf
    exact fnonzero haf.symm
  obtain ⟨w, hw⟩ := prod_poly
  use a⁻¹ • w
  have:  (φ.baseChange F[X]) (a⁻¹ • (w: V[F])) =
      (a⁻¹)^2 • (φ.baseChange F[X]) w := by
      have h2 (c: F)(u: F[X]): c^2 • u = (Polynomial.C c)*(Polynomial.C c) • u := by
        rw[pow_two]
        show (c * c) • u = Polynomial.C c • Polynomial.C c • u
        rw[smul_smul, <- Polynomial.C_mul, <-PolynomialScalarSmul]
        rfl
      rw[<- TensorPolynomialScalarSmul,h2,QuadraticMap.map_smul,mul_smul]
      rfl
  rw[this]
  have hphiw: (φ.baseChange F[X]) w = a^2 • p := by
    suffices ((φ.baseChange F[X]) w: F(X)) = a^2 • p from ?_
    . have hasf: a ^ 2 • (p: F(X)) = (((a^2 • p): F[X]): F(X)) := by
        exact Eq.symm (algebraMap.coe_smul F F[X] (F(X)) (a ^ 2) p)
      rw[hasf] at this
      rw[<- ConversionIff, this]
    rw[toRatFuncTensor_CommuteQuadraticForm]
    have hw:  f • v = w := by
      exact hw
    rw[<- hw, ExtensionScalarsCommutesWithScalars, QuadraticMap.map_smul, <- RatFunc_coePolynomialMultiplication,
      smul_eq_mul, RatFunc_coePolynomialScalarMultiplication, matches_image, <-haf,  sq,← Polynomial.C_mul,
      ← RatFunc.smul_eq_C_smul]
  rw[hphiw]
  nth_rewrite 2[<- one_smul F p]
  rw[smul_smul]
  have: a⁻¹ ^ 2 * a ^ 2 = 1 := by field_simp
  rw[this]

/--Given `φ: V → F` is Anisotropic, `φ: V[X] → F[X]` is also Anisotropic.-/
theorem AnisotropicExtend {φ: QuadraticForm F V} (h: QuadraticMap.Anisotropic φ) [Invertible (2:F)]:
  QuadraticMap.Anisotropic (φ.baseChange F[X]) := sorry

lemma CancellationLemmaExtensionScalars' {v w: V(F)} {f: F(X)} (hvwf: f • v = f • w) (hf: f ≠ 0) : v=w := by
  rw[<- one_smul (F(X)) v]
  rw[<- one_smul (F(X)) w]
  have: f⁻¹*f = 1 := by
    exact inv_mul_cancel₀ hf
  rw[<- this]
  rw[mul_smul, mul_smul]
  rw[hvwf]


lemma CancellationLemmaExtensionScalars {v w: V(F)} {f: F[X]} (hvwf: f • v = f • w) (hf: f ≠ 0) : v=w := by
  have hf': (f: F(X)) ≠ 0 := by
    intro h
    have: (f: F(X))  =  ((0:F[X]): F(X)) := by
      rw[h]
      simp[RatFunc.coePolynomial]
    rw[ConversionIff] at this
    exact hf this
  rw[ExtensionScalarsCommutesWithScalars, ExtensionScalarsCommutesWithScalars] at hvwf
  exact CancellationLemmaExtensionScalars' hvwf hf'

/-- The degree of `φ(v): F[X]` is at most twice of the degree of `v: V[X]`-/
lemma DegreeQuadraticForm (φ: QuadraticForm F V) (v: PolynomialModule F V)
[Invertible (2:F)]: (φ.baseChange F[X] v).natDegree ≤ 2*v.natDegree := by
  sorry

-- We could instead import from `HyperbolicBilinearForms` but I wanted to avoid dependencies
/-- A pair `e`,`f` is Hyperbolic.

Stated assuming `R` is only a commutative ring to allow use of `F[X]`-/
def hyp_pair {R M: Type*} [CommRing R] [AddCommGroup M] [Module R M]  (β:LinearMap.BilinForm R M) (e f : M) : Prop :=
  β e e = 0  ∧  β f f = 0  ∧  β e f = 1

/-- A hyperbolic pair for the polar form of a quadratic form satisfies nice properties. -/
theorem QuadraticForm_hyp_pair  {R M: Type*} [CommRing R] [AddCommGroup M] [Module R M]
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


lemma exists_bilin_one {e: V} {B: LinearMap.BilinForm F V} (enz: e ≠ 0)
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


theorem hyp_pair_exists_symm {e: V} {β:LinearMap.BilinForm F V} (bsymm : β.IsSymm)
  (hn: LinearMap.BilinForm.Nondegenerate β) (enz : e ≠ 0) (eiso : β e e  = 0) [Invertible (2:F)]:
  ∃ f, hyp_pair β e f := by
    have ⟨v, hv⟩ := exists_bilin_one enz hn
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
theorem Extend_hyp_pair {φ: QuadraticForm F V}[Invertible (2:F)] {e f: V} (h: hyp_pair φ.polarBilin e f):
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
  . have: 1 ⊗ₜ[F] e + 1 ⊗ₜ[F] f = (1 ⊗ₜ (e+f): V[F]) := by
      exact Eq.symm (TensorProduct.tmul_add 1 e f)
    have hef:= h.2.2
    simp_all[QuadraticMap.polar,QuadraticMap.polarBilin,this]

/-- If `M` has a hyperbolic pair `e`, `f` then `Set.range φ = Set.univ`.

Stated only assuming `R` is a commutative ring so it works over `F[X]`-/
theorem QuadraticForm_Entire_if_hyp_pair
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
      have ⟨h1,h2,h3,h4⟩  := QuadraticForm_hyp_pair hef
      rw[h1,h2,h3]
      simp



set_option maxHeartbeats 800000

/-- This formalizes the proof of getting (τ_w(v),f') from (v,w) in the
proof of [Theorem 17.3](https://www.math.ucla.edu/~merkurev/Book/Kniga-final/Kniga.pdf)
-/
protected lemma GetSmallerDegree (p: F[X]) (φ: QuadraticForm F V) (f: F[X]) (v: V(F)) (hf: f.natDegree > 0)
  [Invertible (2: F)] (hvf: isGoodPair p φ v f) (hAnsitropic: QuadraticMap.Anisotropic φ):
  (∃f' v', (isGoodPair p φ v' f') ∧ (f'.natDegree<f.natDegree)) ∨ p ∈ Set.range ⇑(φ.baseChange F[X]) := by
    have hAnsitropic': QuadraticMap.Anisotropic (φ.baseChange F[X]) :=
      AnisotropicExtend hAnsitropic
    obtain ⟨⟨vmulf,h_vmulf⟩,hvp,hf_nonzero⟩ := hvf
    obtain ⟨u,r,hur⟩ := PolynomialModule.DivisionAlgorithm vmulf hf
    by_cases hr_neqzero: r=0
    . rw[hr_neqzero, add_zero] at hur
      obtain ⟨hfu_vmulf_eq, degless⟩ := hur
      right
      use u
      rw[<- ConversionIff, toRatFuncTensor_CommuteQuadraticForm]
      have h_vmulf: f • v = f • u := by
        rw[h_vmulf]
        rw[hfu_vmulf_eq,map_smul]
        simp
      have h_vu_eq: v = u := CancellationLemmaExtensionScalars h_vmulf hf_nonzero
      rw[<- h_vu_eq]
      exact hvp
    left
    -- We could instead let f' = (φ.baseChange F[X]) (PolynomialEquiv r) / f and do other work,
    --  but I thought this would be easier
    have: ∃ f', (φ.baseChange F[X]) r = f * f' := by
      use f*p-f* (φ.baseChange F[X] u)-QuadraticMap.polar (φ.baseChange F[X]) u r
      rw[mul_sub, mul_sub]
      have : f * QuadraticMap.polar (⇑(QuadraticForm.baseChange F[X] φ)) u r
        = (QuadraticForm.baseChange F[X] φ) (PolynomialEquiv (f• u+r)) - f*f*(QuadraticForm.baseChange F[X] φ) u- (QuadraticForm.baseChange F[X] φ) r
            :=
        calc
          f * QuadraticMap.polar (⇑(QuadraticForm.baseChange F[X] φ)) u r
            = QuadraticMap.polar (⇑(QuadraticForm.baseChange F[X] φ)) (f • PolynomialEquiv u) r
              := by
              rw[QuadraticMap.polar_smul_left]
              rfl
          _ = (⇑(QuadraticForm.baseChange F[X] φ)) (f• PolynomialEquiv.toFun u+PolynomialEquiv.toFun r )
              - (⇑(QuadraticForm.baseChange F[X] φ)) (f• PolynomialEquiv u) - (⇑(QuadraticForm.baseChange F[X] φ)) (PolynomialEquiv r)
              := rfl
          _ = (QuadraticForm.baseChange F[X] φ) (PolynomialEquiv.toFun (f• u+r)) - f*f*(QuadraticForm.baseChange F[X] φ) (PolynomialEquiv u) - (QuadraticForm.baseChange F[X] φ) (PolynomialEquiv r)
            := by
            rw[QuadraticMap.map_smul]
            rw[PolynomialEquiv.map_add']
            rw[PolynomialEquiv.map_smul']
            simp
          _ = (QuadraticForm.baseChange F[X] φ) (PolynomialEquiv (f• u+r)) - f*f*(QuadraticForm.baseChange F[X] φ) (PolynomialEquiv u) - (QuadraticForm.baseChange F[X] φ) (PolynomialEquiv r)
            := rfl
      rw[this]
      have: (QuadraticForm.baseChange F[X] φ) (PolynomialEquiv (f • u + r)) = f*f*p := by
        rw[<- hur.1, <- ConversionIff, toRatFuncTensor_CommuteQuadraticForm (F := F) (φ := φ)]
        show  (QuadraticForm.baseChange (F(X)) φ) (vmulf) = ↑(f * f * p)
        rw[<- h_vmulf, ExtensionScalarsCommutesWithScalars,QuadraticMap.map_smul, hvp,
          RatFunc_coePolynomialMultiplication, RatFunc_coePolynomialMultiplication]
        rfl
      rw[this]
      ring
    obtain ⟨f', hff'r⟩ := this

    let w := v- u
    let v_reflected: V(F) := HyperplaneReflection (φ.baseChange (F(X))) w v
    use f', v_reflected
    have f'neqzero: f' ≠ 0 := by
      intro hf'eqzero
      rw[hf'eqzero] at hff'r
      have hr_form_eq_zero: (QuadraticForm.baseChange F[X] φ) r= 0 := by
        simp[hff'r ]
      have hr_eq_zero: r=0 := by
        suffices PolynomialEquiv r = 0 from ?_
        . simpa
        exact AnisotropicExtend hAnsitropic _ hr_form_eq_zero
      exact hr_neqzero hr_eq_zero
    constructor; constructor
    . use f'• u + ((φ.baseChange F[X]) u - p) • r

      simp[v_reflected]
      rw[HyperplaneReflection_form (φ.baseChange (F(X))) v w u rfl]
      repeat rw[ExtensionScalarsCommutesWithScalars f']
      rw[smul_add]
      sorry
    . unfold v_reflected
      rw [QuadraticMap.Isometry.map_app]
      exact hvp
    . exact f'neqzero
    . have ⟨hfu_vmulf_eq, degless⟩ := hur
      have h1: f'.natDegree+f.natDegree = (φ.baseChange F[X] r).natDegree := by
        have: f'.natDegree+f.natDegree = (f*f').natDegree := by
          symm
          rw[Polynomial.natDegree_mul']
          exact Nat.add_comm f.natDegree f'.natDegree
          have h1: f.leadingCoeff ≠ 0 := by
            exact Polynomial.leadingCoeff_ne_zero.mpr hf_nonzero
          have h2: f'.leadingCoeff ≠ 0 := by
            exact Polynomial.leadingCoeff_ne_zero.mpr f'neqzero
          simp[h1,h2]
        rw[hff'r]
        omega
      have h2: ((φ.baseChange F[X]) r).natDegree ≤ 2 * r.natDegree := by
        exact DegreeQuadraticForm φ r
      omega

/-- Main lemma for use in CasselsPfisterTheorem. Do not directly use outside. -/
protected lemma CasselsPfisterTheorem_NontrivialContainmentExtension (φ: QuadraticForm F V) [Invertible (2: F)]
  (hn: LinearMap.BilinForm.Nondegenerate (QuadraticMap.polarBilin φ)):
  (algebraMap F[X] (F(X)))⁻¹' (Set.range (φ.baseChange (F(X))))
  ⊆ Set.range (φ.baseChange F[X]) := by
  intro p hp
  let vf := OptimalPair φ p hp
  let v := vf.1
  let f := vf.2
  have hvf: isGoodPair p φ v f := OptimalPair_isGoodPair φ p hp

  by_cases hanisotropic: QuadraticMap.Anisotropic φ
  . by_cases hf_degree: f.natDegree=0
    . apply in_BaseChangePolynomialModule_of_isGoodPair_constant p φ v f hf_degree hvf
    . have: f.natDegree>0 := Nat.zero_lt_of_ne_zero hf_degree
      obtain ⟨f',v', hIsGoodPair',hdegreeless⟩ | _ := CasselsPfister.GetSmallerDegree p φ f v this hvf hanisotropic
      . exfalso
        apply OptimalPair_isOptimal φ p hp f' v' hIsGoodPair' hdegreeless
      . assumption
  . have hisotropic: ∃ v, φ v = 0 ∧ v ≠ 0 := by
      unfold QuadraticMap.Anisotropic at hanisotropic
      push_neg at hanisotropic
      exact hanisotropic
    obtain ⟨v, isotropic_v, hv_neqzero⟩ := hisotropic
    have: ∃ e f, hyp_pair φ.polarBilin e f := by
      use v
      have isotropic_v' : ((QuadraticMap.polarBilin φ) v) v = 0 := by
        simp[isotropic_v]
      apply hyp_pair_exists_symm _ hn hv_neqzero isotropic_v'
      intro a b
      simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, RingHom.id_apply]
      abel_nf
    obtain ⟨e,f,hef⟩ := this
    obtain ⟨e',f',hef'⟩ := Extend_hyp_pair hef
    rw[QuadraticForm_Entire_if_hyp_pair (φ.baseChange F[X]) hef']
    trivial


/-- Lemma for use in CasselsPfisterTheorem. Do not directly use outside. -/
protected lemma CasselsPfisterTheorem_TrivialContainmentExtension (φ: QuadraticForm F V) [Invertible (2: F)]:
  (algebraMap F[X] (F(X)))⁻¹' (Set.range (φ.baseChange (F(X))))
  ⊇ Set.range (φ.baseChange F[X]) := by
  rintro _ ⟨y, rfl⟩
  simp only [Set.mem_preimage, Set.mem_range]
  use y
  rw[<- toRatFuncTensor_CommuteQuadraticForm]
  rfl

/-- The values taken by the extension of a quadratic map `φ: V → F` to `V(X) → F(X)`
    that are in `F[X]` are taken by the extension `V[X] → F[X]` as well.

    *Auxillary version of `CasselsPfisterTheorem` which requires `φ` is `Nondegenerate`*
-/
theorem CasselsPfisterTheoremAux (φ: QuadraticForm F V) [Invertible (2: F)] (hn: LinearMap.BilinForm.Nondegenerate (QuadraticMap.polarBilin φ)):
  (↑)⁻¹' (Set.range (φ.baseChange (F(X))))
   = Set.range (φ.baseChange F[X]) := by
  apply le_antisymm
  . apply CasselsPfister.CasselsPfisterTheorem_NontrivialContainmentExtension φ hn
  . apply CasselsPfister.CasselsPfisterTheorem_TrivialContainmentExtension

/-- The values taken by the extension of a quadratic map `φ: V → F` to `V(X) → F(X)`
    that are in `F[X]` are taken by the extension `V[X] → F[X]` as well.
-/
theorem CasselsPfisterTheorem (φ: QuadraticForm F V) [Invertible (2: F)] (hn: (QuadraticMap.polarBilin φ).Nondegenerate):
  (↑)⁻¹' (Set.range (φ.baseChange (F(X))))
   = Set.range (φ.baseChange F[X]) := sorry


end CasselsPfister
