/-
...
-/
import Mathlib.Algebra.GroupWithZero.Regular
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Definitions
import VERSEIM2025.PolynomialModuleDegree.Definitions
/-!

# Lemmas for calculating the degree of univariate polynomials

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

variable {F V: Type*} {a b c d : F} {n m : ℕ} {u v w : V}

variable [Field F] [AddCommGroup V] [Module F V] {p: F[X]} {vp wp up : PolynomialModule F V}

theorem degree_lt_wf : WellFounded fun vp wp : PolynomialModule F V => degree vp < degree wp :=
  InvImage.wf degree wellFounded_lt

instance : WellFoundedRelation (PolynomialModule F V) :=
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

theorem natDegree_lt_natDegree {wp : PolynomialModule F V} (hp : vp ≠ 0) (hpq : vp.degree < wp.degree) :
    vp.natDegree < wp.natDegree := by
  by_cases hq : wp = 0
  · exact (not_lt_bot <| hq ▸ hpq).elim
  rwa [degree_eq_natDegree hp, degree_eq_natDegree hq, Nat.cast_lt] at hpq

lemma natDegree_eq_natDegree {wp : PolynomialModule F V} (hpq : vp.degree = wp.degree) :
    vp.natDegree = wp.natDegree := by simp [natDegree, hpq]

theorem coeff_eq_zero_of_degree_lt (h : degree vp < n) : vp n = 0 :=
  Classical.not_not.1 (mt le_degree_of_ne_zero (not_le_of_gt h))

theorem coeff_eq_zero_of_natDegree_lt {vp : PolynomialModule F V} {n : ℕ} (h : vp.natDegree < n) :
    vp n = 0 := by
  apply coeff_eq_zero_of_degree_lt
  by_cases hp : vp = 0
  · subst hp
    exact WithBot.bot_lt_coe n
  · rwa [degree_eq_natDegree hp, Nat.cast_lt]

theorem ext_iff_natDegree_le {vp wp : PolynomialModule F V} {n : ℕ} (hp : vp.natDegree ≤ n) (hq : wp.natDegree ≤ n) :
    vp = wp ↔ ∀ i ≤ n, vp i = wp i := by
  sorry
  -- refine Iff.trans PolynomialModule.ext_iff ?_
  -- refine forall_congr' fun i => ⟨fun h _ => h, fun h => ?_⟩
  -- refine (le_or_gt i n).elim h fun k => ?_
  -- exact
  --   (coeff_eq_zero_of_natDegree_lt (hp.trans_lt k)).trans
  --     (coeff_eq_zero_of_natDegree_lt (hq.trans_lt k)).symm

theorem ext_iff_degree_le {vp wp : PolynomialModule F V} {n : ℕ} (hp : vp.degree ≤ n) (hq : wp.degree ≤ n) :
    vp = wp ↔ ∀ i ≤ n, vp i = wp i :=
  ext_iff_natDegree_le (natDegree_le_of_degree_le hp) (natDegree_le_of_degree_le hq)

@[simp]
theorem coeff_natDegree_succ_eq_zero {vp : PolynomialModule F V} : vp (vp.natDegree + 1) = 0 :=
  coeff_eq_zero_of_natDegree_lt (lt_add_one _)

-- We need the explicit `Decidable` argument here because an exotic one shows up in a moment!
theorem ite_le_natDegree_coeff (vp : PolynomialModule F V) (n : ℕ) (I : Decidable (n < 1 + natDegree vp)) :
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

theorem coeff_single : (single F n v) m = if n = m then v else 0 := by
  simp [Finsupp.single_apply]

theorem coeff_C : (C F v) n = ite (n = 0) v 0 := by
  convert coeff_single (F := F) (V := V) (v := v) (m := n) (n := 0) using 2
  simp [eq_comm]

#check Polynomial.eq_C_of_degree_le_zero

theorem eq_C_of_degree_le_zero (h : degree vp ≤ 0) : vp = C F (vp 0) := by
  suffices ∀ i, vp i = (C F) (vp 0) i from ?_
  . rw[<- DFunLike.coe_fn_eq]
    exact (Set.eqOn_univ ⇑vp ⇑((C F) (vp 0))).mp fun ⦃x⦄ a ↦ this x
  intro i
  match i with
  | 0 =>
    rw[coeff_C]
    simp
  | n+1 =>
    rw [coeff_C, if_neg (Nat.succ_ne_zero _), coeff_eq_zero_of_degree_lt]
    exact h.trans_lt (WithBot.coe_lt_coe.2 n.succ_pos)

theorem eq_C_of_degree_eq_zero (h : degree vp = 0) : vp = C F (vp 0) :=
  eq_C_of_degree_le_zero h.le

theorem degree_le_zero_iff : degree vp ≤ 0 ↔ vp = C F (vp 0) :=
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

theorem degree_add_C (hp : 0 < degree vp) : degree (vp + C F v) = degree vp :=
  add_comm (C F v) vp ▸ degree_add_eq_right_of_degree_lt <| lt_of_le_of_lt degree_C_le hp

theorem C_add : C F (v + w) = C F v + C F w := by
  exact LinearMap.map_add (C F) v w

@[simp] theorem natDegree_add_C {v : V} : (vp + C F v).natDegree = vp.natDegree := by
  rcases eq_or_ne vp 0 with rfl | hp
  · simp
  by_cases hpd : vp.degree ≤ 0
  · rw [eq_C_of_degree_le_zero hpd, ← C_add, natDegree_C, natDegree_C]
  · rw [not_le, degree_eq_natDegree hp, Nat.cast_pos, ← natDegree_C F v] at hpd
    exact natDegree_add_eq_left_of_natDegree_lt hpd


@[simp] theorem natDegree_C_add : (C F v + vp).natDegree = vp.natDegree := by
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

lemma natDegree_eq_of_natDegree_add_lt_left (vp wp : PolynomialModule F V)
    (H : natDegree (vp + wp) < natDegree vp) : natDegree vp = natDegree wp := by
  by_contra h
  cases Nat.lt_or_lt_of_ne h with
  | inl h => exact lt_asymm h (by rwa [natDegree_add_eq_right_of_natDegree_lt h] at H)
  | inr h =>
    rw [natDegree_add_eq_left_of_natDegree_lt h] at H
    exact LT.lt.false H

lemma natDegree_eq_of_natDegree_add_lt_right (vp wp : PolynomialModule F V)
    (H : natDegree (vp + wp) < natDegree wp) : natDegree vp = natDegree wp :=
  (natDegree_eq_of_natDegree_add_lt_left wp vp (add_comm vp wp ▸ H)).symm

lemma natDegree_eq_of_natDegree_add_eq_zero (vp wp : PolynomialModule F V)
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

@[simp]
theorem coeff_smul_degree_add_degree (p: F[X]) (vp : PolynomialModule F V) :
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
    let P (p: F[X]): Prop := (p • (single F n) v) (p.natDegree +
       ((single F n) v).natDegree) = p.leadingCoeff • ((single F n) v).leadingCoeff
    let N := p.natDegree
    have P_0: P 0 := sorry
    have P_C_mul_pow: ∀ (n : ℕ) (r : F), r ≠ 0 → n ≤ N → P (Polynomial.C r * Polynomial.X ^ n) := sorry
    have P_C_add: ∀ (f g : F[X]), f.natDegree < g.natDegree →
      g.natDegree ≤ N → P f → P g → P (f + g) := sorry
    exact Polynomial.induction_with_natDegree_le P p.natDegree P_0 P_C_mul_pow P_C_add p (by rfl)

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
theorem leadingCoeff_X_pow_smul {vp : PolynomialModule F V} {n : ℕ} : leadingCoeff ((Polynomial.X^n: F[X]) • vp) = leadingCoeff vp := by
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
theorem leadingCoeff_X_smul {vp : PolynomialModule F V} : leadingCoeff ((Polynomial.X: F[X]) • vp) = leadingCoeff vp := by
  rw[<- leadingCoeff_X_pow_smul (vp := vp) (n := 1)]
  rw[pow_one]

variable (p) (vp) in
@[simp]
lemma leadingCoeff_smul : leadingCoeff (p • vp) = p.leadingCoeff • leadingCoeff vp := by
  by_cases hp : p = 0
  · simp only [hp, zero_smul, Polynomial.leadingCoeff_zero,leadingCoeff_zero]
  · by_cases hv : vp = 0
    · simp only [hv, smul_zero, leadingCoeff_zero]
    · rw [leadingCoeff_smul']
      exact smul_ne_zero (mt Polynomial.leadingCoeff_eq_zero.1 hp) (mt leadingCoeff_eq_zero.1 hv)

end PolynomialModule
