/-
...
-/
import VERSEIM2025.PolynomialModuleDegree.Operations
/-!
...
-/

noncomputable section

open Finsupp Finset

open scoped Polynomial
open PolynomialModule

namespace PolynomialModule

variable {F V: Type*} {a b c d : F} {n m : ℕ} {u v w : V}

variable [Field F] [AddCommGroup V] [Module F V] {p: F[X]} {vp wp up : PolynomialModule F V}

instance: NoZeroSMulDivisors F[X] (PolynomialModule F V) := by
  rw[noZeroSMulDivisors_iff]
  intro c v h
  by_contra h'
  push_neg at h'
  have: leadingCoeff (c • v) = c.leadingCoeff • leadingCoeff v := by
    rw[leadingCoeff_smul]
  rw[h] at this
  simp only [leadingCoeff_zero] at this
  symm at this
  have: c.leadingCoeff =0 ∨ v.leadingCoeff = 0 := by exact eq_zero_or_eq_zero_of_smul_eq_zero this
  obtain hc | hv := this
  . apply h'.1
    exact Polynomial.leadingCoeff_eq_zero.mp hc
  . apply h'.2
    exact leadingCoeff_eq_zero.mp hv

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

/-- See `DivisionAlgorithm_PolynomialModule`-/
protected lemma DivisionAlgorithmAux (v: PolynomialModule F V) {f: F[X]}
  (n: ℕ) (hnv: v.natDegree =n) (hf: f.natDegree >0):  ∃w r, v = f • w + r ∧ r.natDegree < f.natDegree := by
  induction' n using Nat.strong_induction_on with n h generalizing v
  by_cases hnf: n < f.natDegree
  . use 0, v
    constructor
    . simp
    . rw[hnv]
      exact hnf
  . have hnf: n ≥ f.natDegree := by exact Nat.le_of_not_lt hnf
    let v' := v + f • PolynomialModule.single F (n-f.natDegree) (- f.leadingCoeff⁻¹ • (v n))
    have hv'_dglt: v'.natDegree < n := by
      rw[<- hnv]
      have hv_deg_positive :  v.natDegree > 0 := by omega
      have hv_nonzero : v ≠ 0 := by
        contrapose! hv_deg_positive
        rw[Nat.le_zero,hv_deg_positive, PolynomialModule.natDegree_zero]
      unfold v'
      simp only [neg_smul, PolynomialModule.toFinsupp_single, Finsupp.single_neg, smul_neg,
        gt_iff_lt]
      rw[<- SubNegMonoid.sub_eq_add_neg]
      have leadingCoeff_eq:  v.leadingCoeff = f.leadingCoeff • f.leadingCoeff⁻¹ • v n := by
        rw [@smul_smul]
        suffices f.leadingCoeff * f.leadingCoeff⁻¹=1 from ?_
        . rw[this]
          rw[<- hnv, one_smul]
          rfl
        have: f ≠ 0 := by
          exact Polynomial.ne_zero_of_natDegree_gt hf
        have: f.leadingCoeff ≠ 0 := by
          exact Polynomial.leadingCoeff_ne_zero.mpr this
        rw[mul_inv_cancel₀ this]
      have leadingCoeff_neq: f.leadingCoeff⁻¹ • v n ≠ 0 := by
            intro h
            rw[h, smul_zero] at leadingCoeff_eq
            exact hv_nonzero (PolynomialModule.leadingCoeff_eq_zero.mp leadingCoeff_eq)
      rw[<- PolynomialModule.toFinsupp_single]
      refine PolynomialModule.natDegree_sub_lt ?_ ?_ ?_ ?_
      . rw[PolynomialModule.natDegree_smul']
        . have : DecidableEq V := Classical.decEq _
          rw[PolynomialModule.natDegree_single]
          simp only [leadingCoeff_neq, ↓reduceIte]
          rw[hnv]
          exact Eq.symm (Nat.add_sub_of_le hnf)
        . rw[PolynomialModule.leadingCoeff_single]
          simp only [ne_eq, smul_eq_zero, Polynomial.leadingCoeff_eq_zero, leadingCoeff_neq,
            or_false]
          exact Polynomial.ne_zero_of_natDegree_gt hf
      . intro h
        rw[smul_eq_zero] at h
        contrapose! h
        constructor
        . exact Polynomial.ne_zero_of_natDegree_gt hf
        . rw[<- PolynomialModule.leadingCoeff_ne_zero]
          rw[PolynomialModule.leadingCoeff_single]
          simp only [ne_eq, leadingCoeff_neq, not_false_eq_true]
      . exact hv_deg_positive
      . rw[PolynomialModule.leadingCoeff_smul]
        rw[PolynomialModule.leadingCoeff_single]
        exact leadingCoeff_eq
    obtain ⟨w',r, hw'rv',degless'⟩ := h (v'.natDegree) hv'_dglt v' rfl
    use w'+PolynomialModule.single F (n-f.natDegree) (f.leadingCoeff⁻¹ • (v n))
    use r
    constructor
    . rw[smul_add]
      unfold v' at hw'rv'
      rw[add_assoc]
      nth_rewrite 2[add_comm]
      rw[<- add_assoc, <- sub_eq_iff_eq_add, <- hw'rv']
      simp only [neg_smul, map_neg, smul_neg]
      abel
    . exact degless'


/-- The division algorithm holds in `V[X]` dividing by elements of `F[X]` -/
-- TODO: Reformulate in way more similar to mathlib style (i.e. with v/f and v%f defined and a theorem about them)
lemma DivisionAlgorithm(v: PolynomialModule F V) {f: F[X]} (hf: f.natDegree >0):
  ∃w r, v = f • w + r ∧ r.natDegree < f.natDegree :=
    PolynomialModule.DivisionAlgorithmAux v v.natDegree rfl hf


@[elab_as_elim]
theorem induction_on_max_particular {motive : PolynomialModule F V → Prop} (f : PolynomialModule F V)
    (zero : motive 0) (add : ∀ f g, f ≠ 0 → g ≠ 0 → f.natDegree < g.natDegree → motive f → motive g → motive (f + g))
    (single : ∀ a b, b ≠ 0 → motive (single F a b)) : motive f := by
  -- Finsupp.induction_linear f zero add single'
  induction f using Finsupp.induction_on_max
  case h0 => exact zero
  case ha n v f hf_supp v_neq_zero hf_motive =>
    by_cases hf_zero: f=0
    . rw[hf_zero]
      rw[add_zero]
      exact single n v v_neq_zero
    rw[add_comm]
    apply add
    . exact hf_zero
    . intro h_finsuppv_eq_zero
      have h1: (Finsupp.single n v) n = v := by exact single_eq_same
      have h2: (0: ℕ →₀ V) n = 0 := rfl
      rw[h_finsuppv_eq_zero,h2] at h1
      exact v_neq_zero h1.symm
    . show  natDegree f < natDegree (PolynomialModule.single F n v)
      apply natDegree_lt_natDegree hf_zero
      have: ((PolynomialModule.single F n) v).degree=n := by
        exact degree_single n v_neq_zero
      rw[this]
      unfold degree
      rw[Finset.max_eq_sup_coe]
      rw[Finset.sup_lt_iff]
      . intro b hb
        have h:= hf_supp b hb
        rw[WithBot.lt_def]
        use n; constructor; rfl
        intro a ha
        have: b=a := by exact ENat.coe_inj.mp ha
        rw[this] at h
        exact h
      . exact compareOfLessAndEq_eq_lt.mp rfl

    . exact hf_motive
    . exact single n v v_neq_zero

end PolynomialModule
