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


namespace CasselsPfister

open scoped Polynomial
open scoped RatFunc
open scoped TensorProduct

variable {F V: Type*} [Field F] [AddCommGroup V] [Module F V]

example:= PolynomialModule F V -- V[X]
example:= F[X] ⊗[F] V -- Another way to express V[X] (which is not definitionally equal)

example:= (RatFunc F) ⊗[F] V -- F(X) ⊗ V, e.g. V(X)



noncomputable def linearmapAux: F[X] →ₗ[F] RatFunc F where
  toFun := fun v => v
  map_add' := algebraMap.coe_add
  map_smul' := algebraMap.coe_smul F F[X] (RatFunc F)

/--
Auxillary map `F[X] ⊗[F] V →ₗ[F] RatFunc F ⊗[F] V`. Use `toRatFuncTensor` instead.
-/
protected noncomputable def toRatFuncTensorAux : (F[X] ⊗[F] V) →ₗ[F] (RatFunc F ⊗[F] V) :=
  TensorProduct.map linearmapAux LinearMap.id

/-- The inclusion `F[X] ⊗[F] V →ₗ[F[X]] RatFunc F ⊗[F] V`. -/
noncomputable def toRatFuncTensor: F[X] ⊗[F] V →ₗ[F[X]] RatFunc F ⊗[F] V where
  toFun := CasselsPfister.toRatFuncTensorAux
  map_add' := by
    intro v w
    simp
  map_smul' := by
    intro c v
    dsimp[CasselsPfister.toRatFuncTensorAux]
    sorry
    /- See below result (example) that it commutes if we just want with F; the difficulty is
        extending to F[X]
    -/

example (c: F) (v: F[X] ⊗[F] V): (TensorProduct.map linearmapAux LinearMap.id) (c • v) =
   c • (TensorProduct.map linearmapAux LinearMap.id) v := by
   simp -- exact LinearMap.CompatibleSMul.map_smul (TensorProduct.map linearmapAux LinearMap.id) c v

/-- The map `toRatFuncTensor` is injective. -/
theorem toRatFuncTensor_Injective : Function.Injective (@toRatFuncTensor F V _ _ _):= sorry

/-- The map `toRatFuncTensor` is injective, stated elementwise as an iff. -/
theorem toRatFuncTensor_Injective' (a b: F[X] ⊗[F] V ) : toRatFuncTensor a = toRatFuncTensor b ↔ a=b := by
  have := @toRatFuncTensor_Injective F V _ _ _
  exact Function.Injective.eq_iff this

theorem FooSumWork {α}(v w: α →₀ V) (g : α → V →+ V):
  (v+w).sum (fun a => fun v => g a v) = (v.sum (fun a => fun v => g a v)) + (w.sum (fun a => fun v => g a v)) := by
    exact Finsupp.sum_hom_add_index g

@[simp]
noncomputable def FooFunPolynomial: ℕ → V →ₗ[F] F[X] ⊗[F] V := fun n => {
  toFun := fun v =>  (Polynomial.monomial n 1) ⊗ₜ v
  map_add' := fun a b => TensorProduct.tmul_add ((Polynomial.monomial n) 1) a b
  map_smul' := fun c a => TensorProduct.tmul_smul c ((Polynomial.monomial n) 1) a
}

-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/BigOperators/Finsupp/Basic.html#Finsupp.sum_hom_add_index
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Finsupp/LSum.html#Finsupp.sum_smul_index_linearMap'

-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/TensorProduct/MvPolynomial.html#MvPolynomial.rTensor
--  is relevant (but does things in multivariable polynomials)
noncomputable def PolynomialEquiv: PolynomialModule F V ≃ₗ[F[X]] F[X] ⊗[F] V where
  toFun := fun f => f.sum (fun n => fun v => FooFunPolynomial n v)
  map_add' := sorry
  map_smul' := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry




theorem FooSummWork {α}(v w: α →₀ V) (g : α → V →+ V):
  (v+w).sum (fun a => fun v => g a v) = (v.sum (fun a => fun v => g a v)) + (w.sum (fun a => fun v => g a v)) := by
    exact Finsupp.sum_hom_add_index g

/-- The inclusion `V[X] →ₗ[F[X]] RatFunc F ⊗[F] V` defined as a composition of
`PolynomialModule F V →ₗ[F[X]] F[X] ⊗[F] V` (`PolynomialEquiv.toLinearMap`) and
`F[X] ⊗[F] V →ₗ[F[X]] RatFunc F ⊗[F] V` (`toRatFuncTensor`)
but `PolynomialEquiv` is not yet defined in this file.
 -/
-- f.sum (fun n => fun v => algebraMap (Polynomial F) _ (Polynomial.monomial n 1) ⊗ₜ v)
noncomputable def toRatFuncPolynomialModule: PolynomialModule F V →ₗ[F[X]] RatFunc F ⊗[F] V :=
  toRatFuncTensor ∘ₗ PolynomialEquiv.toLinearMap

/-- The degree of a polynomial `v : V[X]` in `WithBot ℕ` with degree of `0` equal to `⊥`-/
def PolynomialModule_degree (v: PolynomialModule F V): WithBot ℕ :=  v.support.max

/-- The degree of a polynomial `v : V[X]` with degree of `0` equal to `0`-/
def PolynomialModule_degreeNat (v: PolynomialModule F V): ℕ :=  WithBot.unbotD 0 (PolynomialModule_degree v)

/-- The degree defined in `PolynomialModule_degree` agrees with Polynomial notion of degree.-/
example (p: F[X]): p.degree = p.support.max := rfl

/-- Ports over degree notion from `PolynomialModule_degree` via `PolynomialEquiv` isomorphism. -/
noncomputable abbrev TensorPolynomialModule_degree (v: F[X] ⊗[F] V):
  WithBot ℕ :=PolynomialModule_degree (PolynomialEquiv.invFun v)

/-- Constant polynomial a: F in F[X]-/
noncomputable example (a: F): F[X] := Polynomial.C a

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


noncomputable example (Q: QuadraticForm F V) [Invertible (2: F)]:
  QuadraticForm F[X] (F[X] ⊗[F] V) := QuadraticForm.baseChange F[X] Q

noncomputable example (Q: QuadraticForm F V) [Invertible (2: F)]:
  QuadraticForm (RatFunc F) ((RatFunc F) ⊗[F] V) := QuadraticForm.baseChange (RatFunc F)  Q

/-- States that a in F(X) is in F[X]. Implementation details could be worth modifying. -/
def in_polynomial_ring (a: RatFunc F): Prop := Nonempty ((algebraMap F[X] (RatFunc F))⁻¹' {a})

/-- States that `v` in `V(X)=F(X) ⊗[F] V`is in `V[X]`.

  Implementation: `∃ (w : PolynomialModule F V), v = toRatFuncPolynomialModule w`
-/
def in_polynomial_module (v: (RatFunc F) ⊗[F] V): Prop :=
  ∃ (w : PolynomialModule F V), v = toRatFuncPolynomialModule w

/-- v in V(X) and f in F[x] has `f • v ∈ V[X]` and `φ(v)=p`-/
structure isGoodPair (p: F[X]) (φ: QuadraticForm F V) (v: (RatFunc F) ⊗[F] V)(f: F[X]) [Invertible (2: F)]: Prop where
  prod_poly: in_polynomial_module (f • v)
  matches_image : (φ.baseChange (RatFunc F)) v = p
  nonzero: f ≠ 0


/-- The set of `(v,f)` in `(RatFunc F ⊗[F] V) × F[X]` with `isGoodPair p φ v f`, i.e.
- `f • v ∈ V[X]`
- `φ(v)=p`
-/
def CollectionPairs (p: F[X]) (φ: QuadraticForm F V) [Invertible (2: F)]: Set ((RatFunc F ⊗[F] V) × F[X]) :=
  { (v,f) | isGoodPair p φ v f }

theorem NonemptyCollectionPairs (φ: QuadraticForm F V) [Invertible (2: F)] (p: F[X]) (hp:
  p ∈ (algebraMap F[X] (RatFunc F))⁻¹' (Set.range (φ.baseChange (RatFunc F)))): (CollectionPairs p φ).Nonempty
   := by sorry

@[simp]
abbrev degree_pair: ((RatFunc F ⊗[F] V) × F[X]) → ℕ := fun (_,f) => f.natDegree

/-- Picks `(v,f)` in `(RatFunc F ⊗[F] V) × F[X]` such that `f.natDegree` is minimized and
- `f • v ∈ V[X]`
- `φ(v)=p`

See `OptimalPair_isGoodPair` and `OptimalPair_isOptimal` for witnesses to this.
-/
noncomputable def OptimalPair (φ: QuadraticForm F V) [Invertible (2: F)] (p: F[X]) (hp:
  p ∈ (algebraMap F[X] (RatFunc F))⁻¹' (Set.range (φ.baseChange (RatFunc F)))):
  (RatFunc F ⊗[F] V) × F[X] := Function.argminOn degree_pair (CollectionPairs p φ) (NonemptyCollectionPairs φ p hp)

/-- The `OptimalPair` is in the `CollectionPairs` set (i.e. is a good pair) -/
def OptimalPair_inCollectionPairs (φ: QuadraticForm F V) [Invertible (2: F)] (p: F[X]) (hp:
  p ∈ (algebraMap F[X] (RatFunc F))⁻¹' (Set.range (φ.baseChange (RatFunc F)))):
  OptimalPair φ p hp ∈ (CollectionPairs p φ) := Function.argminOn_mem degree_pair (CollectionPairs p φ) (NonemptyCollectionPairs φ p hp)

/-- The `OptimalPair` is a good pair -/
def OptimalPair_isGoodPair (φ: QuadraticForm F V) [Invertible (2: F)] (p: F[X]) (hp:
  p ∈ (algebraMap F[X] (RatFunc F))⁻¹' (Set.range (φ.baseChange (RatFunc F)))):
  isGoodPair p φ (OptimalPair φ p hp).1 (OptimalPair φ p hp).2 := OptimalPair_inCollectionPairs φ p hp

/-- The `OptimalPair` has optimal degree -/
def OptimalPair_isOptimal (φ: QuadraticForm F V) [Invertible (2: F)] (p: F[X]) (hp:
  p ∈ (algebraMap F[X] (RatFunc F))⁻¹' (Set.range (φ.baseChange (RatFunc F))))
  (f: F[X]) (v: (RatFunc F) ⊗[F] V)  (hGoodPair: isGoodPair p φ v f)
  : ¬ f.natDegree< (OptimalPair φ p hp).2.natDegree := by
  suffices ¬ degree_pair (v,f) < degree_pair (OptimalPair φ p hp) from ?_
  . exact this
  apply Function.not_lt_argminOn
  exact hGoodPair


/-- Given `f: F[X]` with `f.natDegree=0` and `v:  (RatFunc F) ⊗[F] V` such that `isGoodPair p φ v f` we have
    `p ∈ Set.range (φ.baseChange F[X])`
-/
def in_BaseChangePolynomialModule_of_isGoodPair_constant (p: F[X]) (φ: QuadraticForm F V) (v: (RatFunc F) ⊗[F] V)
(f: F[X]) (hf: f.natDegree=0) [Invertible (2: F)] (hGoodPair: isGoodPair p φ v f)
: p ∈ Set.range (φ.baseChange F[X]) := sorry

/-- A quadratic form `φ` is `Anisotropic` if `∀ v, φ v = 0 → v = 0`. -/
abbrev Anisotropic {R M: Type*} [CommRing R] [AddCommGroup M] [Module R M]  (φ: QuadraticForm R M):
  Prop := ∀v, φ v = 0 → v=0

/--Given `φ: V → F` is Anisotropic, `φ: V[X] → F[X]` is also Anisotropic.-/
theorem AnisotropicExtend {φ: QuadraticForm F V} (h: Anisotropic φ) [Invertible (2:F)]:
  Anisotropic (φ.baseChange F[X]) := sorry

/-- This formalizes the proof of getting (τ_w(v),f') from (v,w) in the
proof of [Theorem 17.3](https://www.math.ucla.edu/~merkurev/Book/Kniga-final/Kniga.pdf)
-/
protected lemma GetSmallerDegree (p: F[X]) (φ: QuadraticForm F V) (f: F[X]) (v: (RatFunc F) ⊗[F] V) (hf: f.natDegree > 0)
   [Invertible (2: F)] (hvf: isGoodPair p φ v f) (hAnsitropic: Anisotropic φ):
  (∃f' v', (isGoodPair p φ v' f') ∧ (f'.natDegree<f.natDegree)) ∨ p ∈ Set.range ⇑(QuadraticForm.baseChange F[X] φ) := sorry

-- We could instead import from `HyperbolicBilinearForms` but I wanted to avoid dependencies
/-- A pair `e`,`f` is Hyperbolic. Stated assuming `R` is only a commutative ring to allow use of `F[X]`-/
def hyp_pair {R M: Type*} [CommRing R] [AddCommGroup M] [Module R M]  (β:LinearMap.BilinForm R M) (e f : M) : Prop :=
  β e e = 0  ∧  β f f = 0  ∧  β e f = 1

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
  . have: 1 ⊗ₜ[F] e + 1 ⊗ₜ[F] f = (1 ⊗ₜ (e+f): F[X] ⊗[F] V) := by
      exact Eq.symm (TensorProduct.tmul_add 1 e f)
    have hef:= h.2.2
    simp_all[QuadraticMap.polar,QuadraticMap.polarBilin,this]

/-- If `M` has a hyperbolic pair `e`, `f` then `Set.range φ = Set.univ`.

Stated only assuming `R` is a commutative ring so it works over `F[X]`-/
theorem QuadraticForm_Entire_if_hyp_pair
{R M: Type*} [CommRing R] [AddCommGroup M] [Module R M]  (φ: QuadraticForm R M) {e f: M}
  (hef: hyp_pair φ.polarBilin e f):
  Set.range φ = Set.univ := by sorry

noncomputable instance PolynomialRingInvertible2 (R: Type*) [CommRing R] [Invertible (2: R)]: Invertible (2: R[X]) where
  invOf := Polynomial.C (⅟2: R)
  invOf_mul_self := by
    show Polynomial.C ⅟ 2 * Polynomial.C 2 = Polynomial.C 1
    rw[<- Polynomial.C_mul]
    simp
  mul_invOf_self := by
    show Polynomial.C 2 * Polynomial.C ⅟ 2 = Polynomial.C 1
    rw[<- Polynomial.C_mul]
    simp



/-- Main lemma for use in CasselsPfisterTheorem. Do not directly use outside. -/
protected lemma CasselsPfisterTheorem_NontrivialContainmentExtension (φ: QuadraticForm F V) [Invertible (2: F)]
  (hn: LinearMap.BilinForm.Nondegenerate (QuadraticMap.polarBilin φ)):
  (algebraMap F[X] (RatFunc F))⁻¹' (Set.range (φ.baseChange (RatFunc F)))
  ⊆ Set.range (φ.baseChange F[X]) := by
  intro p hp
  let vf := OptimalPair φ p hp
  let v := vf.1
  let f := vf.2
  have hvf: isGoodPair p φ v f := OptimalPair_isGoodPair φ p hp

  by_cases hanisotropic: Anisotropic φ
  . by_cases hf_degree: f.natDegree=0
    . apply in_BaseChangePolynomialModule_of_isGoodPair_constant p φ v f hf_degree hvf
    . have: f.natDegree>0 := Nat.zero_lt_of_ne_zero hf_degree
      obtain ⟨f',v', hIsGoodPair',hdegreeless⟩ | _ := CasselsPfister.GetSmallerDegree p φ f v this hvf hanisotropic
      . exfalso
        apply OptimalPair_isOptimal φ p hp f' v' hIsGoodPair' hdegreeless
      . assumption
  . have hisotropic: ∃ v, φ v = 0 ∧ v ≠ 0 := by
      unfold Anisotropic at hanisotropic
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
  (algebraMap F[X] (RatFunc F))⁻¹' (Set.range (φ.baseChange (RatFunc F)))
  ⊇ Set.range (φ.baseChange F[X]) := sorry

/-- Auxillary version of `CasselsPfisterTheorem` which requires `QuadraticMap.polarBilin φ` is `Nondegenerate`
-/
protected theorem CasselsPfisterTheoremAux (φ: QuadraticForm F V) [Invertible (2: F)] (hn: LinearMap.BilinForm.Nondegenerate (QuadraticMap.polarBilin φ)):
  (algebraMap F[X] (RatFunc F))⁻¹' (Set.range (φ.baseChange (RatFunc F)))
   = Set.range (φ.baseChange F[X]) := by
  apply le_antisymm
  . apply CasselsPfister.CasselsPfisterTheorem_NontrivialContainmentExtension φ hn
  . apply CasselsPfister.CasselsPfisterTheorem_TrivialContainmentExtension

/-- The values taken by the extension of a quadratic map `φ: V → F` to `V(X) → F(X)`
    that are in `F[X]` are taken by the extension `V[X] → F[X]` as well.
-/
theorem CasselsPfisterTheorem (φ: QuadraticForm F V) [Invertible (2: F)] (hn: (QuadraticMap.polarBilin φ).Nondegenerate):
  (algebraMap F[X] (RatFunc F))⁻¹' (Set.range (φ.baseChange (RatFunc F)))
   = Set.range (φ.baseChange F[X]) := sorry


end CasselsPfister
