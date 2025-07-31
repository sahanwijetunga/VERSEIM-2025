--------------------------------------------------------------------------------
/-
Copyright (c) 2025 Clea Bergsman, Katherine Buesing, George McNinch, Sahan Wijetunga. All rights reserved.

Released under the Apache 2.0 license as described in the file LICENSE.

VERSEIM-2025 REU @ Tufts University
-/

import VERSEIM2025.Forms.RationalFunctionFields.Basics
import VERSEIM2025.Forms.QuadraticNondegenerate
import VERSEIM2025.Forms.Hyperbolic.TwoSpaceBasics

namespace CasselsPfister

open scoped Polynomial
open scoped TensorProduct
open scoped PolynomialModule
open RationalFunctionFields

variable {F V: Type*} [Field F] [AddCommGroup V] [Module F V]

set_option maxHeartbeats 800000

/-- Lemma for use in `range_quadratic_polynomial_eq_restrict_rational`. Do not directly use outside. -/
protected lemma foo_foo {φ: QuadraticForm F V} (v: V(F)) (u: PolynomialModule F V) [Invertible (2: F)] (f: F[X])
  (f': F[X]) (r: PolynomialModule F V) (hur: (f: F(X)) • (v-u)=r)
 (hff'r: (QuadraticForm.baseChange F[X] φ) r = f * f') (hf_nonzero: f ≠ 0) (f'neqzero: f' ≠ 0): (f': F(X)) * (φ.baseChange F(X) (v-u))⁻¹=f := by
  have hf: (f: F(X)) ≠ 0 := by
    unfold RatFunc.coePolynomial
    simpa using hf_nonzero
  have hf': (f': F(X)) ≠ 0 := by
    unfold RatFunc.coePolynomial
    simpa using f'neqzero
  suffices h: (QuadraticForm.baseChange F(X) φ) (v - ↑↑u) * f = f' from ?_
  . generalize (((QuadraticForm.baseChange F(X) φ) (v - ↑↑u)))=e at *
    generalize (f': F(X))=a at *
    generalize (f: F(X))=b at *
    suffices e ≠ 0 from ?_
    . rw[<- h]
      field_simp
    intro he
    rw[he, zero_mul] at h
    exact hf' h.symm
  rw[mul_comm]
  suffices (↑f *↑f: F(X)) * (QuadraticForm.baseChange F(X) φ) (v - ↑↑u) = f*↑f' from ?_
  . rw[mul_assoc] at this
    generalize (↑f * (QuadraticForm.baseChange F(X) φ) (v - ↑↑u))=a at *
    generalize (f: F(X))=b at *
    generalize (f': F(X))=c at *
    simp_all
  have: (↑f * ↑f': F(X)) = (f * f': F[X]) := by
    exact Eq.symm (RatFunc_coePolynomialMultiplication f f')
  rw[this,<- hff'r, toRatFuncTensor_CommuteQuadraticForm, <- hur, QuadraticMap.map_smul, smul_eq_mul]

/-- Lemma for use in `range_quadratic_polynomial_eq_restrict_rational`. Do not directly use outside. -/
protected lemma foo {v: V(F)} {φ f} (p: F[X]) [Invertible (2:F)]
(hvp : (QuadraticForm.baseChange F(X) φ) v = ↑p)
(hf_nonzero : f ≠ 0)
(vmulf : PolynomialModule F V)
(h_vmulf : f • v = ↑↑vmulf)
(u r : PolynomialModule F V)
(hur : vmulf = f • u + r ∧ r.natDegree < f.natDegree)
(f' : F[X])
(hff'r : (QuadraticForm.baseChange F[X] φ) ↑r = f * f')
(f'neqzero : f' ≠ 0): (f': F(X)) • (u: V(F)) +
    (f': F(X)) •
      (((QuadraticForm.baseChange F(X) φ) (v - u))⁻¹ *
          ((QuadraticForm.baseChange F(X) φ) u - (QuadraticForm.baseChange F(X) φ) v)) •
        (v-u) =
  ((f' • u + ((QuadraticForm.baseChange F[X] φ) u - p) • r): PolynomialModule F V) := by
  have h1: ((f': F(X)) • u + ((QuadraticForm.baseChange F[X] φ) ↑u - p) • r: V(F)) = ↑↑(f' • u +
     ((QuadraticForm.baseChange F[X] φ) ↑u - p) • r) := by
    unfold coeRatFunc coePolynomialModule
    rw [LinearEquiv.map_add, LinearMap.map_add, <- ExtensionScalarsCommutesWithScalars,
      map_smul,map_smul,map_smul,map_smul]
  have h2:  (↑((QuadraticForm.baseChange F[X] φ) ↑u) - ↑p: F(X)) = ((QuadraticForm.baseChange F[X] φ) ↑u - p: F[X]) := by
    unfold RatFunc.coePolynomial
    rw[map_sub]
  have hur: (f: F(X)) • (v-u)=r := by
    rw[smul_sub, <- ExtensionScalarsCommutesWithScalars, h_vmulf, hur.1,
      <- ExtensionScalarsCommutesWithScalars]
    simp[coeRatFunc, coePolynomialModule]
  rw[<- h1, smul_smul, <- mul_assoc, CasselsPfister.foo_foo v u f f' r hur hff'r hf_nonzero f'neqzero, mul_comm, <- smul_smul, hur, hvp,
    <- toRatFuncTensor_CommuteQuadraticForm, h2, ExtensionScalarsCommutesWithScalars]

/-- This formalizes the proof of getting (τ_w(v),f') from (v,w) in the
proof of [Theorem 17.3](https://www.math.ucla.edu/~merkurev/Book/Kniga-final/Kniga.pdf)
-/
protected lemma GetSmallerDegree (p: F[X]) (φ: QuadraticForm F V) (f: F[X]) (v: V(F)) (hf: f.natDegree > 0)
  [Invertible (2: F)] (hvf: isGoodPair p φ v f) (hAnsitropic: QuadraticMap.Anisotropic φ):
  (∃f' v', (isGoodPair p φ v' f') ∧ (f'.natDegree<f.natDegree)) ∨ p ∈ Set.range ⇑(φ.baseChange F[X]) := by
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
        rw[hfu_vmulf_eq,coePolynomialModule,map_smul]
        simp[coeRatFunc]
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
    have hw_neq_zero: w ≠ 0 := by
      intro hw
      have hv_sub_u_eq_zero: v - u = 0 := hw
      rw[hur.1] at h_vmulf
      unfold coeRatFunc at *
      unfold coePolynomialModule at *
      rw[LinearEquiv.map_add] at h_vmulf
      rw[LinearMap.map_add] at h_vmulf
      have: v = toRatFuncTensor (PolynomialEquiv u) := sub_eq_zero.mp hv_sub_u_eq_zero
      rw[this] at h_vmulf
      rw[LinearEquiv.map_smul] at h_vmulf
      have hr_coe_eq_zero: toRatFuncTensor (PolynomialEquiv r) = 0 := by
        symm at h_vmulf
        rw[LinearMap.map_smul_of_tower, add_eq_left] at h_vmulf
        exact h_vmulf
      suffices r=0 from hr_neqzero this
      suffices h:PolynomialEquiv r=0 from ?_
      . have h : PolynomialEquiv r = PolynomialEquiv 0 := h
        rw[EquivLike.apply_eq_iff_eq] at h
        exact h
      exact (toRatFuncTensor_Injective' (PolynomialEquiv r) 0).mp hr_coe_eq_zero

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

      simp only [v_reflected]
      rw[HyperplaneReflection_form (AnisotropicExtend' hAnsitropic) v hw_neq_zero u rfl]
      repeat rw[ExtensionScalarsCommutesWithScalars f']
      rw[smul_add]
      exact CasselsPfister.foo p hvp hf_nonzero vmulf h_vmulf u r hur f' hff'r f'neqzero
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



/-- Main lemma for use in `range_quadratic_polynomial_eq_restrict_rational`. Do not directly use outside. -/
protected lemma NontrivialContainmentExtension (φ: QuadraticForm F V) [Invertible (2: F)]
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
    have: ∃ e f, HyperbolicTwoSpace.hyp_pair φ.polarBilin e f := by
      use v
      have isotropic_v' : ((QuadraticMap.polarBilin φ) v) v = 0 := by
        simp[isotropic_v]
      apply HyperbolicTwoSpace.Exists _ hn hv_neqzero isotropic_v'
      intro a b
      simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, RingHom.id_apply]
      abel_nf
    obtain ⟨e,f,hef⟩ := this
    obtain ⟨e',f',hef'⟩ := HyperbolicTwoSpace.Extend hef
    rw[HyperbolicTwoSpace.QuadraticForm_Entire (φ.baseChange F[X]) hef']
    trivial


/-- Lemma for use in `range_quadratic_polynomial_eq_restrict_rational`. Do not directly use outside. -/
protected lemma TrivialContainmentExtension (φ: QuadraticForm F V) [Invertible (2: F)]:
  (algebraMap F[X] (F(X)))⁻¹' (Set.range (φ.baseChange (F(X))))
  ⊇ Set.range (φ.baseChange F[X]) := by
  rintro _ ⟨y, rfl⟩
  simp only [Set.mem_preimage, Set.mem_range]
  use y
  rw[<- toRatFuncTensor_CommuteQuadraticForm]
  rfl


/-- The values taken by the extension of a quadratic map `φ: V → F` to `V(X) → F(X)`
    that are in `F[X]` are taken by the extension `V[X] → F[X]` as well.

    *Cassels-Pfister Theorem*
-/
theorem range_quadratic_polynomial_eq_restrict_rational (φ: QuadraticForm F V) [Invertible (2: F)]:
  (↑)⁻¹' (Set.range (φ.baseChange (F(X))))
   = Set.range (φ.baseChange F[X]) := by
  rw[QuadraticForm.range_baseChange_quotient_rad_eq_range_baseChange F(X),
  QuadraticForm.range_baseChange_quotient_rad_eq_range_baseChange F[X] ]
  apply le_antisymm
  . exact CasselsPfister.NontrivialContainmentExtension φ.quotient_rad φ.quotient_rad_nondegenerate
  . exact CasselsPfister.TrivialContainmentExtension φ.quotient_rad


#print axioms range_quadratic_polynomial_eq_restrict_rational


end CasselsPfister
