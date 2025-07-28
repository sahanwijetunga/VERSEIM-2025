/-
...
-/
import Mathlib.Algebra.GroupWithZero.Regular
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Definitions
import VERSEIM2025.PolynomialModuleDegree.Definitions
/-!

# Lemmas for calculating the degree of univariate polynomial modules

## Main results
- `degree_smul'` : The degree of the scalar product is the sum of degrees
- `leadingCoeff_add_of_degree_eq` and `leadingCoeff_add_of_degree_lt` :
    The leading coefficient of a sum is determined by the leading coefficients and degrees

## These results were mostly copied from Polynomial.Degree.Operations with some modifications.
-/

noncomputable section

open Finsupp Finset

open scoped Polynomial
open PolynomialModule

namespace PolynomialModule

variable {R M: Type*} {a b c d : R} {n m : ℕ} {u v w : M}

variable [CommRing R] [AddCommGroup M] [Module R M] {p: R[X]} {vp wp up : PolynomialModule R M}

theorem degree_lt_wf : WellFounded fun vp wp : PolynomialModule R M => degree vp < degree wp :=
  InvImage.wf degree wellFounded_lt

instance : WellFoundedRelation (PolynomialModule R M) :=
  ⟨_, degree_lt_wf⟩

theorem le_natDegree_of_ne_zero (h : vp n ≠ 0) : n ≤ natDegree vp := by
  rw [← Nat.cast_le (α := WithBot ℕ), ← degree_eq_natDegree]
  · exact le_degree_of_ne_zero h
  · rintro rfl
    exact h rfl

theorem degree_eq_of_le_of_coeff_ne_zero (pn : vp.degree ≤ n) (p1 : vp n ≠ 0) : vp.degree = n :=
  pn.antisymm (le_degree_of_ne_zero p1)

theorem natDegree_eq_of_le_of_coeff_ne_zero (pn : vp.natDegree ≤ n) (p1 : vp n ≠ 0) :
    vp.natDegree = n :=
  pn.antisymm (le_natDegree_of_ne_zero p1)

lemma natDegree_eq_natDegree {wp : PolynomialModule R M} (hpq : vp.degree = wp.degree) :
    vp.natDegree = wp.natDegree := by simp [natDegree, hpq]

theorem coeff_eq_zero_of_degree_lt (h : degree vp < n) : vp n = 0 :=
  Classical.not_not.1 (mt le_degree_of_ne_zero (not_le_of_gt h))

theorem coeff_eq_zero_of_natDegree_lt {vp : PolynomialModule R M} {n : ℕ} (h : vp.natDegree < n) :
    vp n = 0 := by
  apply coeff_eq_zero_of_degree_lt
  by_cases hp : vp = 0
  · subst hp
    exact WithBot.bot_lt_coe n
  · rwa [degree_eq_natDegree hp, Nat.cast_lt]

theorem ext_iff_natDegree_le {vp wp : PolynomialModule R M} {n : ℕ} (hp : vp.natDegree ≤ n) (hq : wp.natDegree ≤ n) :
    vp = wp ↔ ∀ i ≤ n, vp i = wp i := by
  constructor; tauto
  intro h
  suffices ∀ i, vp i = wp i from Finsupp.ext this
  intro i
  rcases le_or_gt i n with hi_le_n | hn_lt_i
  . exact h i hi_le_n
  have h1: vp i = 0 := by
    refine coeff_eq_zero_of_natDegree_lt ?_
    omega
  have h2: wp i = 0 := by
    refine coeff_eq_zero_of_natDegree_lt ?_
    omega
  rw[h1,h2]

theorem ext_iff_degree_le {vp wp : PolynomialModule R M} {n : ℕ} (hp : vp.degree ≤ n) (hq : wp.degree ≤ n) :
    vp = wp ↔ ∀ i ≤ n, vp i = wp i :=
  ext_iff_natDegree_le (natDegree_le_of_degree_le hp) (natDegree_le_of_degree_le hq)

@[simp]
theorem coeff_natDegree_succ_eq_zero {vp : PolynomialModule R M} : vp (vp.natDegree + 1) = 0 :=
  coeff_eq_zero_of_natDegree_lt (lt_add_one _)

-- We need the explicit `Decidable` argument here because an exotic one shows up in a moment!
theorem ite_le_natDegree_coeff (vp : PolynomialModule R M) (n : ℕ) (I : Decidable (n < 1 + natDegree vp)) :
    @ite _ (n < 1 + natDegree vp) I (vp n) 0 = vp n := by
  split_ifs with h
  · rfl
  · exact (coeff_eq_zero_of_natDegree_lt (not_le.1 fun w => h (Nat.lt_one_add_iff.2 w))).symm

theorem coeff_natDegree_eq_zero_of_degree_lt (h : degree vp < degree wp) :
    vp (natDegree wp) = 0 :=
  coeff_eq_zero_of_degree_lt (lt_of_lt_of_le h degree_le_natDegree)

theorem ne_zero_of_degree_gt {n : WithBot ℕ} (h : n < degree vp) : vp ≠ 0 :=
  mt degree_eq_bot.2 h.ne_bot

theorem ne_zero_of_degree_ge_degree (hpq : vp.degree ≤ wp.degree) (hp : vp ≠ 0) : wp ≠ 0 :=
  ne_zero_of_degree_gt
    (lt_of_lt_of_le (bot_lt_iff_ne_bot.mpr (by rwa [Ne, degree_eq_bot])) hpq :
      wp.degree > ⊥)

theorem ne_zero_of_natDegree_gt {n : ℕ} (h : n < natDegree vp) : vp ≠ 0 := fun H => by
  simp [H] at h

theorem degree_lt_degree (h : natDegree vp < natDegree wp) : degree vp < degree wp := by
  by_cases hp : vp = 0
  · simp only [hp, degree_zero]
    rw [bot_lt_iff_ne_bot]
    intro hq
    simp [hp, degree_eq_bot.mp hq] at h
  · rwa [degree_eq_natDegree hp, degree_eq_natDegree <| ne_zero_of_natDegree_gt h, Nat.cast_lt]

theorem natDegree_lt_natDegree_iff (hp : vp ≠ 0) : natDegree vp < natDegree wp ↔ degree vp < degree wp :=
  ⟨degree_lt_degree, fun h ↦ by
    have hq : wp ≠ 0 := ne_zero_of_degree_gt h
    rwa [degree_eq_natDegree hp, degree_eq_natDegree hq, Nat.cast_lt] at h⟩

theorem coeff_single : (single R n v) m = if n = m then v else 0 := by
  simp [Finsupp.single_apply]

theorem coeff_C : (C R v) n = ite (n = 0) v 0 := by
  convert coeff_single (R := R) (M := M) (v := v) (m := n) (n := 0) using 2
  simp [eq_comm]

theorem eq_C_of_degree_le_zero (h : degree vp ≤ 0) : vp = C R (vp 0) := by
  suffices ∀ i, vp i = (C R) (vp 0) i from ?_
  . rw[<- DFunLike.coe_fn_eq]
    exact (Set.eqOn_univ ⇑vp ⇑((C R) (vp 0))).mp fun ⦃x⦄ a ↦ this x
  intro i
  match i with
  | 0 =>
    rw[coeff_C]
    simp
  | n+1 =>
    rw [coeff_C, if_neg (Nat.succ_ne_zero _), coeff_eq_zero_of_degree_lt]
    exact h.trans_lt (WithBot.coe_lt_coe.2 n.succ_pos)

theorem eq_C_of_degree_eq_zero (h : degree vp = 0) : vp = C R (vp 0) :=
  eq_C_of_degree_le_zero h.le

theorem degree_le_zero_iff : degree vp ≤ 0 ↔ vp = C R (vp 0) :=
  ⟨eq_C_of_degree_le_zero, fun h => h.symm ▸ degree_C_le⟩

theorem degree_add_eq_left_of_degree_lt (h : degree wp < degree vp) : degree (vp + wp) = degree vp :=
  le_antisymm (max_eq_left_of_lt h ▸ degree_add_le _ _) <|
    degree_le_degree <| by
      rw [add_apply, coeff_natDegree_eq_zero_of_degree_lt h, add_zero]
      exact mt leadingCoeff_eq_zero.1 (ne_zero_of_degree_gt h)

theorem degree_add_eq_right_of_degree_lt (h : degree vp < degree wp) : degree (vp + wp) = degree wp := by
  rw [add_comm, degree_add_eq_left_of_degree_lt h]

theorem natDegree_add_eq_left_of_degree_lt (h : degree wp < degree vp) :
    natDegree (vp + wp) = natDegree vp :=
  natDegree_eq_of_degree_eq (degree_add_eq_left_of_degree_lt h)

theorem natDegree_add_eq_left_of_natDegree_lt (h : natDegree wp < natDegree vp) :
    natDegree (vp + wp) = natDegree vp :=
  natDegree_add_eq_left_of_degree_lt (degree_lt_degree h)

theorem natDegree_add_eq_right_of_degree_lt (h : degree vp < degree wp) :
    natDegree (vp + wp) = natDegree wp :=
  natDegree_eq_of_degree_eq (degree_add_eq_right_of_degree_lt h)

theorem natDegree_add_eq_right_of_natDegree_lt (h : natDegree vp < natDegree wp) :
    natDegree (vp + wp) = natDegree wp :=
  natDegree_add_eq_right_of_degree_lt (degree_lt_degree h)

theorem degree_add_C (hp : 0 < degree vp) : degree (vp + C R v) = degree vp :=
  add_comm (C R v) vp ▸ degree_add_eq_right_of_degree_lt <| lt_of_le_of_lt degree_C_le hp

theorem C_add : C R (v + w) = C R v + C R w := by
  exact LinearMap.map_add (C R) v w

@[simp] theorem natDegree_add_C {v : M} : (vp + C R v).natDegree = vp.natDegree := by
  rcases eq_or_ne vp 0 with rfl | hp
  · simp
  by_cases hpd : vp.degree ≤ 0
  · rw [eq_C_of_degree_le_zero hpd, ← C_add, natDegree_C, natDegree_C]
  · rw [not_le, degree_eq_natDegree hp, Nat.cast_pos, ← natDegree_C R v] at hpd
    exact natDegree_add_eq_left_of_natDegree_lt hpd


@[simp] theorem natDegree_C_add : (C R v + vp).natDegree = vp.natDegree := by
  simp [add_comm _ vp]

theorem degree_add_eq_of_leadingCoeff_add_ne_zero (h : leadingCoeff vp + leadingCoeff wp ≠ 0) :
    degree (vp + wp) = max vp.degree wp.degree :=
  le_antisymm (degree_add_le _ _) <|
    match lt_trichotomy (degree vp) (degree wp) with
    | Or.inl hlt => by
      rw [degree_add_eq_right_of_degree_lt hlt, max_eq_right_of_lt hlt]
    | Or.inr (Or.inl HEq) =>
      le_of_not_gt fun hlt : max (degree vp) (degree wp) > degree (vp + wp) =>
        h <|
          show leadingCoeff vp + leadingCoeff wp = 0 by
            rw [HEq, max_self] at hlt
            rw [leadingCoeff, leadingCoeff, natDegree_eq_of_degree_eq HEq, ← add_apply]
            exact coeff_natDegree_eq_zero_of_degree_lt hlt
    | Or.inr (Or.inr hlt) => by
      rw [degree_add_eq_left_of_degree_lt hlt, max_eq_left_of_lt hlt]

lemma natDegree_eq_of_natDegree_add_lt_left (vp wp : PolynomialModule R M)
    (H : natDegree (vp + wp) < natDegree vp) : natDegree vp = natDegree wp := by
  by_contra h
  cases Nat.lt_or_lt_of_ne h with
  | inl h => exact lt_asymm h (by rwa [natDegree_add_eq_right_of_natDegree_lt h] at H)
  | inr h =>
    rw [natDegree_add_eq_left_of_natDegree_lt h] at H
    exact LT.lt.false H

lemma natDegree_eq_of_natDegree_add_lt_right (vp wp : PolynomialModule R M)
    (H : natDegree (vp + wp) < natDegree wp) : natDegree vp = natDegree wp :=
  (natDegree_eq_of_natDegree_add_lt_left wp vp (add_comm vp wp ▸ H)).symm

lemma natDegree_eq_of_natDegree_add_eq_zero (vp wp : PolynomialModule R M)
    (H : natDegree (vp + wp) = 0) : natDegree vp = natDegree wp := by
  by_cases h₁ : natDegree vp = 0; on_goal 1 => by_cases h₂ : natDegree wp = 0
  · exact h₁.trans h₂.symm
  · apply natDegree_eq_of_natDegree_add_lt_right; rwa [H, Nat.pos_iff_ne_zero]
  · apply natDegree_eq_of_natDegree_add_lt_left; rwa [H, Nat.pos_iff_ne_zero]


theorem leadingCoeff_add_of_degree_lt (h : degree vp < degree wp) :
    leadingCoeff (vp + wp) = leadingCoeff wp := by
  have : vp (natDegree wp) = 0 := coeff_natDegree_eq_zero_of_degree_lt h
  simp only [leadingCoeff, natDegree_eq_of_degree_eq (degree_add_eq_right_of_degree_lt h), this,
    add_apply, zero_add]

theorem leadingCoeff_add_of_degree_lt' (h : degree wp < degree vp) :
    leadingCoeff (vp + wp) = leadingCoeff vp := by
  rw [add_comm]
  exact leadingCoeff_add_of_degree_lt h

theorem leadingCoeff_add_of_degree_eq (h : degree vp = degree wp)
    (hlc : leadingCoeff vp + leadingCoeff wp ≠ 0) :
    leadingCoeff (vp + wp) = leadingCoeff vp + leadingCoeff wp := by
  have : natDegree (vp + wp) = natDegree vp := by
    apply natDegree_eq_of_degree_eq
    rw [degree_add_eq_of_leadingCoeff_add_ne_zero hlc, h, max_self]
  simp only [leadingCoeff, this, natDegree_eq_of_degree_eq h, add_apply]



/-simpa only [degree, ← support_toFinsupp, toFinsupp_mul]
    using AddMonoidAlgebra.sup_support_mul_le (WithBot.coe_add _ _).le _ _
-/
theorem degree_smul_le (p: R[X]) (vp : (PolynomialModule R M)) : degree (p • vp) ≤ p.degree + degree vp := by
  refine (degree_le_iff_coeff_zero (p • vp) (p.degree + vp.degree)).mpr ?_
  intro n h
  rw[PolynomialModule.smul_apply]
  suffices (∀ x ∈ antidiagonal n, p.coeff x.1 • vp x.2=0 ) from ?_
  . exact sum_eq_zero this
  intro x hx
  have: p.degree < x.1 ∨ vp.degree < x.2 := by
    rw[mem_antidiagonal] at hx
    have: p.degree + vp.degree < x.1+x.2 := by
      exact lt_of_lt_of_eq h (congrArg Nat.cast (id (Eq.symm hx)))
    exact lt_or_lt_of_add_lt_add this
  rcases this with hp_deglt_x1 | hvp_deglt_x2
  . have: p.coeff x.1 = 0 := by
      exact Polynomial.coeff_eq_zero_of_degree_lt hp_deglt_x1
    rw[this, zero_smul]
  . have: vp x.2=0 := by
      exact coeff_eq_zero_of_degree_lt hvp_deglt_x2
    rw[this, smul_zero]

theorem degree_smul_le_of_le {a b : WithBot ℕ} (hp : p.degree ≤ a) (hv : degree vp ≤ b) :
    degree (p • vp) ≤ a + b :=
  (vp.degree_smul_le _).trans <| add_le_add ‹_› ‹_›

@[simp]
theorem leadingCoeff_single (v : M) (n : ℕ) : leadingCoeff (single R n v) = v := by
  classical
  by_cases hv : v = 0
  · simp only [hv, (single R n).map_zero, leadingCoeff_zero]
  · rw [leadingCoeff, natDegree_single, if_neg hv]
    simp

theorem leadingCoeff_X_pow_smul_C (v : M) (n : ℕ) : leadingCoeff ((Polynomial.X^n: R[X]) • C R v) = v := by
  rw [X_pow_smul_C_eq_single, leadingCoeff_single]

theorem leadingCoeff_X_smul_C (v : M) : leadingCoeff ((Polynomial.X: R[X]) • C R v) = v := by
  simpa only [pow_one] using leadingCoeff_X_pow_smul_C v 1

@[simp]
theorem leadingCoeff_C (v : M) : leadingCoeff (C R v) = v :=
  leadingCoeff_single v 0

theorem natDegree_smul_le {vp : (PolynomialModule R M)} : natDegree (p • vp) ≤ p.natDegree + natDegree vp := by
  apply natDegree_le_of_degree_le
  apply le_trans (degree_smul_le p vp)
  rw [Nat.cast_add]
  apply add_le_add
  . exact Polynomial.degree_le_natDegree
  . apply degree_le_natDegree

theorem natDegree_smul_le_of_le (hp : p.natDegree ≤ m) (hv : natDegree vp ≤ n) :
    natDegree (p • vp) ≤ m + n :=
natDegree_smul_le.trans <| add_le_add ‹_› ‹_›


@[simp]
theorem coeff_smul_degree_add_degree (p: R[X]) (vp : PolynomialModule R M) :
(p • vp) (p.natDegree + natDegree vp) = p.leadingCoeff • leadingCoeff vp := by
  induction vp using PolynomialModule.induction_on_max_particular with
  | zero => simp
  | add  vp wp vp_neq_zero wp_neq_zero hvw_deg_lt hv_motive hw_motive =>
    have h1: (vp+wp).leadingCoeff = wp.leadingCoeff := by
      rw[leadingCoeff_add_of_degree_lt]
      exact (natDegree_lt_natDegree_iff vp_neq_zero).mp hvw_deg_lt
    have h2: (p • vp) (p.natDegree + wp.natDegree)= 0 := by
      refine coeff_eq_zero_of_natDegree_lt ?_
      have:  (p • vp).natDegree ≤ p.natDegree + vp.natDegree := natDegree_smul_le
      omega
    rw[natDegree_add_eq_right_of_natDegree_lt hvw_deg_lt, h1,
      smul_add, add_apply, h2, hw_motive, zero_add]
  | single n v v_neq_zero =>
    induction p using Polynomial.induction_with_natDegree_le (N := p.natDegree)
    case single.P_0 => simp
    case single.P_C_mul_pow k a a_neq_zero _ =>
      rw[Polynomial.C_mul_X_pow_eq_monomial, PolynomialModule.monomial_smul_single, Polynomial.natDegree_monomial_eq k a_neq_zero,
        @Polynomial.leadingCoeff_monomial, natDegree_single_eq n v_neq_zero, @leadingCoeff_single,
        single_apply]
      simp
    case single.P_C_add f g fg_deg_lt _ hf hg=>
      generalize (single R n) v=vp at *
      have h1: (f+g).leadingCoeff = g.leadingCoeff := by
        by_cases hf_zero: f=0
        . rw[hf_zero, zero_add]
        rw[Polynomial.leadingCoeff_add_of_degree_lt]
        exact (Polynomial.natDegree_lt_natDegree_iff hf_zero).mp fg_deg_lt
      have h2: (f • vp) (g.natDegree + vp.natDegree)= 0 := by
        refine coeff_eq_zero_of_natDegree_lt ?_
        have:  (f • vp).natDegree ≤ f.natDegree + vp.natDegree := natDegree_smul_le
        omega
      rw[Polynomial.natDegree_add_eq_right_of_natDegree_lt fg_deg_lt, h1,
        add_smul, add_apply, h2, zero_add, hg]
    case single.a => rfl

theorem degree_smul' (h : p.leadingCoeff • leadingCoeff vp ≠ 0):
    degree (p • vp) = p.degree + degree vp :=
  have hp : vp ≠ 0 := by refine mt ?_ h; exact fun hp => by rw [hp, leadingCoeff_zero, smul_zero]
  have hq : p ≠ 0 := by refine mt ?_ h; exact fun hq => by rw [hq, Polynomial.leadingCoeff_zero, zero_smul]
  le_antisymm (degree_smul_le p vp)
    (by
      rw [degree_eq_natDegree hp, Polynomial.degree_eq_natDegree hq]
      refine le_degree_of_ne_zero (n := p.natDegree + natDegree vp) ?_
      rwa [coeff_smul_degree_add_degree])

theorem natDegree_smul' (h :  p.leadingCoeff • leadingCoeff vp ≠ 0) :
    natDegree (p • vp) = p.natDegree + natDegree vp :=
  have hv : vp ≠ 0 := mt leadingCoeff_eq_zero.2 fun h₁ => h <| by rw [h₁, smul_zero]
  have hp : p ≠ 0 := mt Polynomial.leadingCoeff_eq_zero.2 fun h₁ => h <| by rw [h₁, zero_smul]
  natDegree_eq_of_degree_eq_some <| by
    rw [degree_smul' h, Nat.cast_add, degree_eq_natDegree hv, Polynomial.degree_eq_natDegree hp]

theorem leadingCoeff_smul' (h : p.leadingCoeff • leadingCoeff vp ≠ 0) :
    leadingCoeff (p • vp) = p.leadingCoeff • leadingCoeff vp := by
  unfold leadingCoeff
  rw [natDegree_smul' h, coeff_smul_degree_add_degree]
  rfl


@[simp]
theorem leadingCoeff_X_pow_smul {vp : PolynomialModule R M} {n : ℕ}
  [NoZeroSMulDivisors R M] [NeZero (1: R)] : leadingCoeff ((Polynomial.X^n: R[X]) • vp) = leadingCoeff vp := by
  by_cases hvp: vp=0
  . rw[hvp]
    simp
  rw[leadingCoeff_smul' _]
  . rw [Polynomial.leadingCoeff_X_pow, one_smul]
  refine smul_ne_zero ?_ ?_
  . rw [@Polynomial.leadingCoeff_X_pow]
    exact one_ne_zero
  exact leadingCoeff_ne_zero.mpr hvp

@[simp]
theorem leadingCoeff_X_smul {vp : PolynomialModule R M}
[NoZeroSMulDivisors R M] [NeZero (1: R)] : leadingCoeff ((Polynomial.X: R[X]) • vp) = leadingCoeff vp := by
  rw[<- leadingCoeff_X_pow_smul (vp := vp) (n := 1)]
  rw[pow_one]

variable (p) (vp) in
@[simp]
lemma leadingCoeff_smul [NoZeroSMulDivisors R M] : leadingCoeff (p • vp) = p.leadingCoeff • leadingCoeff vp := by
  by_cases hp : p = 0
  · simp only [hp, zero_smul, Polynomial.leadingCoeff_zero,leadingCoeff_zero]
  · by_cases hv : vp = 0
    · simp only [hv, smul_zero, leadingCoeff_zero]
    · rw [leadingCoeff_smul']
      exact smul_ne_zero (mt Polynomial.leadingCoeff_eq_zero.1 hp) (mt leadingCoeff_eq_zero.1 hv)

end PolynomialModule
