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

namespace RationalFunctionFields

open scoped Polynomial
open scoped TensorProduct
open scoped PolynomialModule


scoped[RationalFunctionFields] notation:9000 F "(X)" => RatFunc F
scoped[RationalFunctionFields] notation:1000 V "[" F:1000 "]" => F[X] ⊗[F] V
scoped[RationalFunctionFields] notation:1000 V "(" F:1000 ")"  => F(X) ⊗[F] V

variable {F V: Type*} [Field F] [AddCommGroup V] [Module F V]

theorem ConversionIff (a b: F[X]): (a: F(X))=b ↔ a=b := by
  constructor
  . intro h
    apply IsFractionRing.coe_inj.mp h
  . intro h
    rw[h]

theorem ExtensionScalarsCommutesWithScalars (p: F[X]) (v: V(F) ) : p • v = (p: F(X)) • v := by
  unfold RatFunc.coePolynomial
  rw [@IsScalarTower.algebraMap_smul]


theorem PolynomialScalarSmul (c: F) (u: F[X]): (Polynomial.C c) * u = c • u := by
  exact Polynomial.C_mul' c u

theorem TensorPolynomialScalarSmul (c: F) (u: V[F]): (Polynomial.C c) • u = c • u := by
  rw [Polynomial.C_eq_algebraMap, IsScalarTower.algebraMap_smul]

theorem RatFunc_coePolynomialMultiplication (f g: F[X]): (f*g: F[X]) = (f: F(X))*(g: F(X)) := by
  unfold RatFunc.coePolynomial
  rw [← algebraMap.coe_mul]

theorem RatFunc_coePolynomialScalarMultiplication (f: F[X]) (g: F(X)): ↑f * g = f • g:= by
  rw [@Algebra.smul_def',@mul_eq_mul_right_iff]; left
  rfl

/-- Maps `V[X] → V(X)` in the sense of extension by scalars using tensor products-/
noncomputable def toRatFuncTensor: V[F] →ₗ[F[X]] V(F) :=
  TensorProduct.AlgebraTensorModule.map (Algebra.linearMap F[X] (F(X))) LinearMap.id

@[coe]
noncomputable def coeRatFunc: V[F] → V(F) := toRatFuncTensor

noncomputable scoped instance : Coe (V[F]) (V(F)) := ⟨coeRatFunc⟩


/-- The map `toRatFuncTensor` is injective. -/
theorem toRatFuncTensor_Injective : Function.Injective (toRatFuncTensor (F := F) (V := V)):= by
  have: (toRatFuncTensor: V[F] → V(F))
   = TensorProduct.map (AlgHom.toLinearMap (Algebra.algHom F F[X] F(X))) LinearMap.id := rfl
  rw[this]
  rw[<- LinearMap.rTensor_def]
  exact Module.Flat.rTensor_preserves_injective_linearMap (hf := RatFunc.algebraMap_injective F)

theorem RatFunc_CoePolynomial_add (a b: F[X]): ↑(a+b)=(a+b: F(X)) := by
  exact algebraMap.coe_add a b

theorem RatVec_CoeVec_add (v w: V[F]): ↑(v+w)=(v+w: V(F)) := by
  unfold coeRatFunc toRatFuncTensor
  rw[LinearMap.map_add]

noncomputable instance RatFuncInvertible2 [Invertible (2: F)]: Invertible (2: F(X)) where
  invOf := RatFunc.C (⅟2: F)
  invOf_mul_self := by
    have h1: (2: F(X))=RatFunc.C (2:F) := by
      simp only [<- one_add_one_eq_two,map_add, map_one]
    have h2: (1: F(X))=RatFunc.C (1:F) := by simp
    have h3: (⅟ 2 * 2: F) = 1 := by
      simp
    rw[h1,h2, <- RingHom.map_mul,h3]
  mul_invOf_self := by
    have h1: (2: F(X))=RatFunc.C (2:F) := by
      simp only [<- one_add_one_eq_two,map_add, map_one]
    have h2: (1: F(X))=RatFunc.C (1:F) := by simp
    have h3: (2*⅟ 2: F) = 1 := by
      simp
    rw[h1,h2, <- RingHom.map_mul,h3]

theorem toRatFuncTensor_CommuteAssociateForm_Pure (φ: QuadraticForm F V) [Invertible (2:F)] (v w: V) (a b: F[X]):
  QuadraticMap.associated (φ.baseChange F[X]) (a ⊗ₜ v) (b ⊗ₜ w) =
    QuadraticMap.associated (φ.baseChange F(X)) (a ⊗ₜ v) (b ⊗ₜ w) := by
  repeat rw[QuadraticForm.associated_baseChange]
  generalize (QuadraticMap.associated φ)=B
  repeat rw[LinearMap.BilinForm.baseChange_tmul]
  rw[Eq.symm (PolynomialScalarSmul _ _)]
  rw[RatFunc.smul_eq_C_mul]
  simp[RatFunc.coePolynomial]

theorem toRatFuncTensor_CommuteAssociateForm (φ: QuadraticForm F V) [Invertible (2:F)] (v w: V[F]):
   ↑(QuadraticMap.associated (QuadraticForm.baseChange F[X] φ) v w) =
  QuadraticMap.associated (QuadraticForm.baseChange F(X) φ) v w  := by
  induction v using TensorProduct.induction_on with
  | zero => simp[coeRatFunc,RatFunc.coePolynomial]
  | tmul a v =>
    induction w using TensorProduct.induction_on with
    | zero => simp[coeRatFunc,RatFunc.coePolynomial]
    | tmul b w => exact toRatFuncTensor_CommuteAssociateForm_Pure φ v w a b
    | add w w' hw hw' =>
      rw[LinearMap.BilinForm.add_right, RatFunc_CoePolynomial_add,
        hw, hw', RatVec_CoeVec_add, LinearMap.BilinForm.add_right]
  | add v v' hv hv' =>
    rw[LinearMap.BilinForm.add_left, RatFunc_CoePolynomial_add,
      hv, hv', RatVec_CoeVec_add, LinearMap.BilinForm.add_left]

/-- The map `toRatFuncTensor` commutes with quadratic forms. -/
theorem toRatFuncTensor_CommuteQuadraticForm (φ: QuadraticForm F V) (v: (V[F])) [Invertible (2:F)]:
φ.baseChange F[X] v = (φ.baseChange F(X)) v := by
  rw[<- QuadraticMap.associated_eq_self_apply F[X]]
  rw[<- QuadraticMap.associated_eq_self_apply F(X)]
  exact toRatFuncTensor_CommuteAssociateForm φ v v

/-- The map `toRatFuncTensor` is injective, stated elementwise as an iff. -/
theorem toRatFuncTensor_Injective' (a b: V[F] ) : (a: V(F)) = b ↔ a=b := by
  have := @toRatFuncTensor_Injective F V _ _ _
  exact Function.Injective.eq_iff this


/-- An isomorphism between the two notions of `V[X]`-/
noncomputable def PolynomialEquiv: PolynomialModule F V ≃ₗ[F[X]] V[F]
  := (PolyEquiv.PolynomialModuleEquivTensorProduct (R := F) (M := V)).symm

@[coe]
noncomputable abbrev coePolynomialModule: PolynomialModule F V → V[F] := PolynomialEquiv

noncomputable scoped instance : Coe (PolynomialModule F V) (V[F]) := ⟨coePolynomialModule⟩

theorem PolynomialEquivSingleConstant (v: V): (PolynomialModule.single F 0) v = (1 ⊗ₜ v: V[F]) := by
  simp only [coePolynomialModule, DFunLike.coe, EquivLike.coe, PolynomialEquiv,
    PolynomialModule.single, Finsupp.singleAddHom]
  simp[PolyEquiv.PolynomialModuleEquivTensorProduct]

theorem PolynomialEquivSingle (v: V) (n: ℕ): (PolynomialModule.single F n) v = ((Polynomial.monomial n 1) ⊗ₜ v: V[F]) := by
  simp only [coePolynomialModule, DFunLike.coe, EquivLike.coe, PolynomialEquiv,
    PolynomialModule.single, Finsupp.singleAddHom]
  simp[PolyEquiv.PolynomialModuleEquivTensorProduct]


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

theorem HyperplaneReflection_form {φ: QuadraticForm F V} (hanisotropic: QuadraticMap.Anisotropic φ) (v: V) {w: V} (hw: w ≠ 0) (u: V) (huvw: w=v-u):
  HyperplaneReflection φ w v = u + ((φ w)⁻¹ * (φ u - φ v)) • w := by
    simp only [HyperplaneReflection,QuadraticMap.Isometry.instFunLike,
      LinearMap.coe_mk, AddHom.coe_mk]
    simp only [huvw ]
    rw[sub_eq_add_neg, <- neg_smul,neg_mul_eq_neg_mul]
    rw[<- QuadraticMap.polar_neg_right]
    rw[QuadraticMap.polar]
    rw[sub_eq_add_neg _ u, add_assoc, add_comm (-u) (-v), <- add_assoc, add_neg_cancel,
      zero_add,QuadraticMap.map_neg _ u,QuadraticMap.map_neg _ v]
    have hneqzero: φ (v + -u) ≠ 0 := by
      rw[<- sub_eq_add_neg]
      rw[<- huvw ]
      exact fun a ↦ hw (hanisotropic w a)
    generalize φ (v + -u) =a, φ v =b, φ u =c at *
    repeat rw[sub_eq_add_neg]
    have: v + (-1: F) • (v + -u)=u := by
      simp
    rw[add_assoc, add_comm (-a) (-b), <- add_assoc, add_mul, <- neg_mul_eq_neg_mul,
      CommGroupWithZero.mul_inv_cancel _ hneqzero, add_smul, add_comm _ (-1 • (v + -u)),
      <- add_assoc, this, mul_comm]

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
  dsimp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,coeRatFunc,coePolynomialModule ]
  rw[map_add,hv,hw]
  simp[coeRatFunc,coePolynomialModule]

theorem in_polynomial_module_smul {v: V(F)} (p: F[X]) (hv: in_polynomial_module v):
   in_polynomial_module (p • v) := by
  obtain ⟨v', hv⟩ := hv
  use p • v'
  dsimp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,coeRatFunc,coePolynomialModule]
  rw[map_smul,hv]
  simp[coeRatFunc,coePolynomialModule]

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
      show f.denom • f ⊗ₜ[F] v = ↑(f.num • ((PolynomialModule.single F 0) v): V[F])
      rw[PolynomialEquivSingleConstant, ExtensionScalarsCommutesWithScalars]
      have: ↑f.denom • f ⊗ₜ[F] v  = (↑f.denom • f) ⊗ₜ[F] v  := by
        exact rfl
      rw[TensorProduct.smul_tmul' ]
      rw[TensorProduct.smul_tmul' ]
      show ((f.denom: F(X)) * f) ⊗ₜ[F] v = ↑((f.num • (1: F[X])) ⊗ₜ[F] v)
      have : (↑f.denom * f) = ((f.num) * 1: F[X])  := by
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
      rw[this]
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


theorem PolynomialModule_coe_add(u v: PolynomialModule F V): (u+v: V[F])=(u+v: PolynomialModule F V) := by
    unfold coePolynomialModule
    rw[LinearEquiv.map_add]

theorem DegreeBilinForm (B : LinearMap.BilinMap F V F)(n m : ℕ) {v w: V} (hv: v ≠ 0) (hw: w ≠ 0):
 (((LinearMap.BilinForm.baseChange F[X] B) ((PolynomialModule.single F n) v))
      ((PolynomialModule.single F m) w)).natDegree ≤
  ((PolynomialModule.single F n) v).natDegree + ((PolynomialModule.single F m) w).natDegree
  := by
  repeat rw[PolynomialEquivSingle]
  rw[LinearMap.BilinForm.baseChange_tmul]
  have h1: ((Polynomial.monomial n) 1 * (Polynomial.monomial m) 1: F[X]).natDegree = n+m := by
    rw[Polynomial.monomial_mul_monomial, one_mul]
    exact Polynomial.natDegree_monomial_eq (n + m) one_ne_zero
  have h2:  ((PolynomialModule.single F n) v).natDegree = n := by
    exact PolynomialModule.natDegree_single_eq n hv
  have h3:  ((PolynomialModule.single F m) w).natDegree = m := by
    exact PolynomialModule.natDegree_single_eq m hw
  have h4:  ((B v) w • ((Polynomial.monomial n) 1 * (Polynomial.monomial m) 1: F[X])).natDegree
    ≤ ((Polynomial.monomial n) 1 * (Polynomial.monomial m) 1: F[X]).natDegree := by
    exact Polynomial.natDegree_smul_le _ _
  rw[h2,h3]
  omega

theorem DegreeAssociateToQuadraticForm (φ: QuadraticForm F V) [Invertible (2:F)] (v w: PolynomialModule F V):
   (QuadraticMap.associated (QuadraticForm.baseChange F[X] φ) v w).natDegree ≤ v.natDegree + w.natDegree:= by
  rw[QuadraticForm.associated_baseChange]
  generalize (QuadraticMap.associated φ)=B
  induction v using PolynomialModule.induction_on_max_particular with
  | zero => simp
  | add f g _ _ hfg hf hg =>
    -- hfg' holds as they both equal g.natDegree since f.natDegree < g.natDegree
    have hfg': (f+g).natDegree = g.natDegree := by
      exact PolynomialModule.natDegree_add_eq_right_of_natDegree_lt hfg
    rw[hfg']
    rw[<- PolynomialModule_coe_add]
    rw[LinearMap.BilinForm.add_left]
    have h1:  (((LinearMap.BilinForm.baseChange F[X] B) f) ↑w + ((LinearMap.BilinForm.baseChange F[X] B) g) ↑w).natDegree
      ≤ max (((LinearMap.BilinForm.baseChange F[X] B) f) ↑w).natDegree (((LinearMap.BilinForm.baseChange F[X] B) g) ↑w).natDegree
      := Polynomial.natDegree_add_le _ _
    generalize (LinearMap.BilinForm.baseChange F[X] B)=C at *
    omega
  | single n v v_neq_zero =>
    induction w using PolynomialModule.induction_on_max_particular with
    | zero => simp
    | add f g _ _ hfg hf hg =>
      generalize ((PolynomialModule.single F n) v)=v at *
      have hfg': (f+g).natDegree = g.natDegree := by
        exact PolynomialModule.natDegree_add_eq_right_of_natDegree_lt hfg
      rw[hfg']
      rw[<- PolynomialModule_coe_add]
      rw[LinearMap.BilinForm.add_right]
      have h1:  ( LinearMap.BilinForm.baseChange F[X] B v f + LinearMap.BilinForm.baseChange F[X] B v g).natDegree
        ≤ max (LinearMap.BilinForm.baseChange F[X] B v f).natDegree (LinearMap.BilinForm.baseChange F[X] B v g).natDegree
        := Polynomial.natDegree_add_le (LinearMap.BilinForm.baseChange F[X] B v f) (LinearMap.BilinForm.baseChange F[X] B v g)
      generalize (LinearMap.BilinForm.baseChange F[X] B)=C at *
      omega
    | single m w w_neq_zero => exact DegreeBilinForm B n m v_neq_zero w_neq_zero


/-- The degree of `φ(v): F[X]` is at most twice of the degree of `v: V[X]`-/
lemma DegreeQuadraticForm (φ: QuadraticForm F V) (v: PolynomialModule F V)
[Invertible (2:F)]: (φ.baseChange F[X] v).natDegree ≤ 2*v.natDegree := by
  rw[<- QuadraticMap.associated_eq_self_apply F[X]]
  have: 2 * v.natDegree=v.natDegree+v.natDegree := Nat.two_mul v.natDegree
  rw[this]
  exact DegreeAssociateToQuadraticForm φ v v

protected lemma foo_polarpolarbilinextendeq {φ: QuadraticForm F V} [Invertible (2:F)]
  (x y: V[F]):
   (QuadraticMap.polar (⇑(QuadraticForm.baseChange F[X] φ)) x y) = LinearMap.BilinForm.baseChange
    F[X] (QuadraticMap.polarBilin φ) x y := by
    rw[<- QuadraticForm.polarBilin_baseChange]
    simp

theorem QuadraticFormExtensionPolynomial (φ: QuadraticForm F V)[Invertible (2:F)]
  (v: PolynomialModule F V):  ((QuadraticForm.baseChange F[X] φ) ↑v).coeff (2 * v.natDegree) = φ v.leadingCoeff
  := by
  let n := v.natDegree
  show ((QuadraticForm.baseChange F[X] φ) ↑v).coeff (2 * n) = φ v.leadingCoeff
  nth_rewrite 1[<- Finsupp.sum_single v]
  unfold coePolynomialModule
  unfold Finsupp.sum
  rw[map_sum]
  rw[QuadraticMap.map_sum]
  rw[Polynomial.coeff_add]
  have h1: (∑ i ∈ v.support, (QuadraticForm.baseChange F[X] φ)
    (PolynomialEquiv (Finsupp.single i (v i)))).coeff (2 * n) = φ v.leadingCoeff := by
    rw[Polynomial.finset_sum_coeff]
    have (k: ℕ): (Finsupp.single k (v k))= (PolynomialModule.single F k) (v k) := rfl
    have h1 (k: ℕ): (QuadraticForm.baseChange F[X] φ) (PolynomialEquiv (Finsupp.single k (v k)))
      =  Polynomial.monomial (2*k) (φ (v k)) := by
      rw[this, <- coePolynomialModule, PolynomialEquivSingle, QuadraticForm.baseChange_tmul,
        Polynomial.monomial_mul_monomial, mul_one, two_mul, Polynomial.smul_monomial, smul_eq_mul, mul_one]
    have h2: φ v.leadingCoeff =
      ((QuadraticForm.baseChange F[X] φ) (PolynomialEquiv (Finsupp.single n (v n)))).coeff (2 * n) := by
      rw[h1, Polynomial.coeff_monomial_same]
      rfl
    rw[h2]
    by_cases hv_zero: v=0
    . have h1: v.support = ∅ := Finsupp.support_eq_empty.mpr hv_zero
      have h2: v n = 0 := by rw[hv_zero, Finsupp.coe_zero, Pi.zero_apply]
      rw[h1, h2]
      simp
    apply Finset.sum_eq_single_of_mem n
    . unfold n
      rw[Finsupp.mem_support_iff, <- PolynomialModule.leadingCoeff, PolynomialModule.leadingCoeff_ne_zero]
      exact hv_zero
    intro i hi hi_neq_n
    rw[h1]
    apply Polynomial.coeff_monomial_of_ne
    omega
  have h2: (∑ ij ∈ v.support.sym2 with ¬ij.IsDiag,
          QuadraticMap.polarSym2 (⇑(QuadraticForm.baseChange F[X] φ))
            (Sym2.map (fun x ↦ PolynomialEquiv (Finsupp.single x (v x))) ij)).coeff (2*n) = 0 := by
    rw[Polynomial.finset_sum_coeff]
    apply Finset.sum_eq_zero
    intro b
    induction b using Sym2.inductionOn with
    | hf x y =>
    have h1 (i: ℕ): (PolynomialEquiv (Finsupp.single i (v i)): V[F]) = (PolynomialModule.single F i) (v i) := by
     rw [PolynomialModule.toFinsupp_single]
    have h2: ((Polynomial.monomial x) 1 * (Polynomial.monomial y) 1) = (Polynomial.monomial (x+y) 1: F[X]) := by
      rw [@Polynomial.monomial_mul_monomial, mul_one]
    have h3 (a: F) (k: ℕ): a • (Polynomial.monomial k 1) = Polynomial.monomial k a := by
      rw[Polynomial.smul_monomial, smul_eq_mul, mul_one]
    intro hxy
    have: (¬v x = 0 ∧ ¬v y = 0) ∧ ¬x = y := by simpa using hxy
    obtain ⟨⟨ (hx: v x ≠ 0),(hy: v y ≠ 0)⟩, (hxy: x ≠  y)⟩ := this
    rw [Sym2.map_pair_eq, QuadraticMap.polarSym2_sym2Mk,
      RationalFunctionFields.foo_polarpolarbilinextendeq, h1 x, h1 y, PolynomialEquivSingle,
      PolynomialEquivSingle, LinearMap.BilinForm.baseChange_tmul, h2, h3,
      Polynomial.coeff_monomial_of_ne]
    have hxn: x ≤ n := PolynomialModule.le_natDegree_of_ne_zero hx
    have hyn: y ≤ n := PolynomialModule.le_natDegree_of_ne_zero hy
    omega
  rw[h1,h2, add_zero]

/--Given `φ: V → F` is Anisotropic, `φ: V[X] → F[X]` is also Anisotropic.-/
theorem AnisotropicExtend {φ: QuadraticForm F V} (h: QuadraticMap.Anisotropic φ) [Invertible (2:F)]:
  QuadraticMap.Anisotropic (φ.baseChange F[X]) := by
  unfold QuadraticMap.Anisotropic
  suffices ∀ (v: PolynomialModule F V), (QuadraticForm.baseChange F[X] φ) v = 0 → v = 0 from ?_
  . intro x
    intro hx
    let v := PolynomialEquiv.invFun x
    have hvx: x = v := by
      rw[<- EquivLike.inv_apply_eq_iff_eq_apply]
      rfl
    have hv_form: (QuadraticForm.baseChange F[X] φ) v=0 := by
      rw[<- hvx, hx]
    have hv_eqzero: v=0 := this v hv_form
    rw[hvx, hv_eqzero]
    simp
  intro v
  intro hv
  suffices v.leadingCoeff = 0 from ?_
  . exact PolynomialModule.leadingCoeff_eq_zero.mp this
  apply h
  rw[<- QuadraticFormExtensionPolynomial φ v, hv]
  simp

/--Given `φ: V → F` is Anisotropic, `φ: V(X) → F(X)` is also Anisotropic.-/
theorem AnisotropicExtend' {φ: QuadraticForm F V} (h: QuadraticMap.Anisotropic φ) [Invertible (2:F)]:
  QuadraticMap.Anisotropic (φ.baseChange F(X)) := by
  intro v hv
  obtain ⟨f, ⟨w, hwvf⟩ , hf⟩ := exists_denominator v
  have hw: φ.baseChange F[X] w = 0 := by
    suffices ( (QuadraticForm.baseChange F[X] φ) ↑w = (0: F(X) ) ) from ?_
    . have h': (0: F[X])=(0: F(X)) := by simp[RatFunc.coePolynomial]
      rw[<- h'] at this
      unfold RatFunc.coePolynomial at this
      exact (ConversionIff _ _).mp this
    rw[toRatFuncTensor_CommuteQuadraticForm, <- hwvf, ExtensionScalarsCommutesWithScalars,
      QuadraticMap.map_smul, hv, smul_zero]
  have: w=0 := by
    have h1: (w: V[F])=0 := by
      exact (AnisotropicExtend h) w hw
    have h2: (0: V[F])=(0: PolynomialModule F V) := rfl
    rw[h2] at h1
    rw[EquivLike.apply_eq_iff_eq] at h1
    exact h1
  rw[this] at hwvf
  simp only [coeRatFunc, map_zero] at hwvf
  exact CancellationLemmaExtensionScalars hwvf hf

theorem QuadraticFormDegree (φ: QuadraticForm F V)[Invertible (2:F)]
  (v: PolynomialModule F V) (hv: φ v.leadingCoeff ≠ 0):
  ((QuadraticForm.baseChange F[X] φ) ↑v).natDegree = 2*v.natDegree := by
    apply le_antisymm
    . exact DegreeQuadraticForm φ v
    refine Polynomial.le_natDegree_of_mem_supp (2 * v.natDegree) ?_
    rw[Polynomial.mem_support_iff, QuadraticFormExtensionPolynomial]
    exact hv

theorem AnisotropicFormDegree {φ: QuadraticForm F V} (h: φ.Anisotropic) [Invertible (2:F)]
  (v: PolynomialModule F V): ((QuadraticForm.baseChange F[X] φ) v).natDegree = 2*v.natDegree := by
    by_cases hv: v=0
    . rw[hv]
      simp
    apply le_antisymm
    . exact DegreeQuadraticForm φ v
    refine Polynomial.le_natDegree_of_mem_supp (2 * v.natDegree) ?_
    rw[Polynomial.mem_support_iff, QuadraticFormExtensionPolynomial]
    contrapose! hv
    rw[<- PolynomialModule.leadingCoeff_eq_zero]
    exact h _ hv

end RationalFunctionFields
