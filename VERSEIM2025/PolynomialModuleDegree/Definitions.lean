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
/-!
# Degree of univariate polynomials

## Main definitions

* `PolynomialModule.degree`: the degree of a polynomial vector, where `0` has degree `⊥`
* `PolynomialModule.natDegree`: the degree of a polynomial vector, where `0` has degree `0`
* `PolynomialModule.leadingCoeff`: the leading coefficient of a polynomial module
* `PolynomialModule.nextCoeff`: the next coefficient after the leading coefficient

## Main results

* `PolynomialModule.degree_eq_natDegree`: the degree and natDegree coincide for nonzero polynomial vectors

## These results were mostly copied from Polynomial.Degree.Definitions with some modifications.
-/

noncomputable section

open Finsupp Finset

open scoped Polynomial
open PolynomialModule

namespace PolynomialModule

variable {F V: Type*} {a b c d : F} {n m : ℕ} {u v w : V}

variable [Field F] [AddCommGroup V] [Module F V] {p: F[X]} {vp wp up : PolynomialModule F V}

/-- `degree vp` is the degree of the polynomial vector `vp`, i.e. the largest `X`-exponent in `vp`.
`degree vp = some n` when `vp ≠ 0` and `n` is the highest power of `X` that appears in `vp`, otherwise
`degree 0 = ⊥`. -/
def degree (vp : PolynomialModule F V) : WithBot ℕ :=
  vp.support.max

/-- `natDegree vp` forces `degree vp` to ℕ, by defining `natDegree 0 = 0`. -/
def natDegree (vp : (PolynomialModule F V)) : ℕ :=
  (degree vp).unbotD 0

/-- `leadingCoeff vp` gives the coefficient of the highest power of `X` in `vp`. -/
def leadingCoeff (vp : (PolynomialModule F V)) : V :=
  vp (natDegree vp)

@[simp]
theorem degree_zero : degree (0 : (PolynomialModule F V)) = ⊥ :=
  rfl

@[simp]
theorem natDegree_zero : natDegree (0 : (PolynomialModule F V)) = 0 :=
  rfl

@[simp]
theorem coeff_natDegree : vp (natDegree vp) = leadingCoeff vp :=
  rfl

@[simp]
theorem degree_eq_bot : degree vp = ⊥ ↔ vp = 0 :=
  ⟨fun h => support_eq_empty.1 (Finset.max_eq_bot.1 h), fun h => h.symm ▸ rfl⟩

theorem degree_ne_bot : degree vp ≠ ⊥ ↔ vp ≠ 0 := degree_eq_bot.not

theorem degree_eq_natDegree (hv : vp ≠ 0) : degree vp = (natDegree vp : WithBot ℕ) := by
  let ⟨n, hn⟩ := not_forall.1 (mt Option.eq_none_iff_forall_not_mem.2 (mt degree_eq_bot.1 hv))
  have hn : degree vp = some n := Classical.not_not.1 hn
  rw [natDegree, hn]; rfl

theorem degree_eq_iff_natDegree_eq {vp : (PolynomialModule F V)} {n : ℕ} (hv : vp ≠ 0) :
    vp.degree = n ↔ vp.natDegree = n := by rw [degree_eq_natDegree hv]; exact WithBot.coe_eq_coe

theorem degree_eq_iff_natDegree_eq_of_pos {vp : (PolynomialModule F V)} {n : ℕ} (hn : 0 < n) :
    vp.degree = n ↔ vp.natDegree = n := by
  obtain rfl|h := eq_or_ne vp 0
  · simp [hn.ne]
  · exact degree_eq_iff_natDegree_eq h

theorem natDegree_eq_of_degree_eq_some {vp : (PolynomialModule F V)} {n : ℕ} (h : degree vp = n) : natDegree vp = n := by
  rw [natDegree, h, Nat.cast_withBot, WithBot.unbotD_coe]

theorem degree_ne_of_natDegree_ne {n : ℕ} : vp.natDegree ≠ n → degree vp ≠ n :=
  mt natDegree_eq_of_degree_eq_some

theorem natDegree_eq_of_degree_eq (h : degree vp = degree wp) :
    natDegree vp = natDegree wp := by unfold natDegree; rw [h]

@[simp]
theorem degree_le_natDegree : degree vp ≤ natDegree vp :=
  WithBot.giUnbotDBot.gc.le_u_l _

theorem le_degree_of_ne_zero (h : vp n ≠ 0) : (n : WithBot ℕ) ≤ degree vp := by
  rw [Nat.cast_withBot]
  exact Finset.le_sup (mem_support_iff.2 h)

theorem degree_mono{f g: (PolynomialModule F V)} (h : f.support ⊆ g.support) :
    f.degree ≤ g.degree :=
  Finset.sup_mono h

theorem degree_le_degree (h : wp (natDegree vp) ≠ 0) : degree vp ≤ degree wp := by
  by_cases hv : vp = 0
  · rw [hv, degree_zero]
    exact bot_le
  · rw [degree_eq_natDegree hv]
    exact le_degree_of_ne_zero h

theorem natDegree_le_iff_degree_le {n : ℕ} : natDegree vp ≤ n ↔ degree vp ≤ n :=
  WithBot.unbotD_le_iff (fun _ ↦ bot_le)

theorem natDegree_lt_iff_degree_lt (hv : vp ≠ 0) : vp.natDegree < n ↔ vp.degree < ↑n :=
  WithBot.unbotD_lt_iff (absurd · (degree_eq_bot.not.mpr hv))

alias ⟨degree_le_of_natDegree_le, natDegree_le_of_degree_le⟩ := natDegree_le_iff_degree_le

theorem natDegree_le_natDegree  {wp : PolynomialModule F V} (hpq : vp.degree ≤ wp.degree) :
    vp.natDegree ≤ wp.natDegree :=
  WithBot.giUnbotDBot.gc.monotone_l hpq

variable (F) in
abbrev C: V →ₗ[F] PolynomialModule F V := lsingle F 0

theorem support_lsingle (n) {v : V} (H : v ≠ 0) : (lsingle F n v).support = singleton n := by
  rw [support]
  exact Finsupp.support_single_ne_zero _ H

@[simp]
theorem degree_C (hv : v ≠ 0) : degree (C F v) = (0 : WithBot ℕ) := by
  rw [degree, C , support_lsingle 0 hv, max_eq_sup_coe, sup_singleton,
    WithBot.coe_zero]

theorem degree_C_le : degree (C F v) ≤ 0 := by
  by_cases h : v = 0
  · rw [h]
    simp
  · rw [degree_C h]

theorem degree_C_lt : degree (C F v) < 1 :=
  degree_C_le.trans_lt <| WithBot.coe_lt_coe.mpr zero_lt_one

variable (F) in
@[simp]
theorem natDegree_C (v : V) : natDegree (C F v) = 0 := by
  by_cases hv : v = 0
  · have : C F v = 0 := by simp[hv]
    rw [natDegree, degree_eq_bot.2 this, WithBot.unbotD_bot]
  · rw [natDegree, degree_C hv, WithBot.unbotD_zero]

@[simp]
theorem toFinsupp_single (n : ℕ) (v : V) : single F n v = Finsupp.single n v := by
  simp [single ]
  rw [← @singleAddHom_apply]
  rfl

@[simp]
theorem ofFinsupp_single (n : ℕ) (v : V) : (Finsupp.single n v : PolynomialModule F V) = single F n v := by
  rw[toFinsupp_single]

theorem support_single (n) {v : V} (H : v ≠ 0) : (single F n v).support = singleton n := by
  rw [← ofFinsupp_single, support]; exact Finsupp.support_single_ne_zero _ H

@[simp]
theorem degree_single (n : ℕ) (hv : v ≠ 0) : degree (single F n v) = n := by
  rw [degree, support_single n hv, max_singleton, Nat.cast_withBot]

theorem X_pow_smul_C_eq_single : ∀ {n : ℕ}, (Polynomial.X ^ n: F[X]) • C F v = single F n v
  | 0 => by
    simp only [pow_zero, C, lsingle, one_smul, toFinsupp_single]
    exact rfl
  | n + 1 => by
    rw [pow_succ, mul_comm, ← smul_smul, X_pow_smul_C_eq_single,
      Polynomial.X , PolynomialModule.monomial_smul_single, add_comm 1 n, one_smul]

variable (F) in
@[simp]
theorem degree_X_pow_smul_C (n : ℕ) (hv : v ≠ 0): degree ((Polynomial.X ^ n: F[X]) • C F v) = n := by
  rw [X_pow_smul_C_eq_single, degree_single n hv]

variable (F) in
theorem degree_X_smul_C (hv : v ≠ 0) : degree ((Polynomial.X: F[X]) • C F v) = 1 := by
  simpa only [pow_one] using degree_X_pow_smul_C F (1: ℕ) hv

theorem degree_single_le (n : ℕ) (v : V) : degree (single F n v) ≤ n :=
  letI := Classical.decEq V
  if h : v = 0 then by rw [h, (single F n).map_zero, degree_zero]; exact bot_le
  else le_of_eq (degree_single n h)

theorem degree_X_pow_smul_C_le (n : ℕ) (v : V) : degree ((Polynomial.X ^n : F[X]) • C F v) ≤ n := by
  rw [X_pow_smul_C_eq_single]
  apply degree_single_le

theorem degree_X_smul_C_le (v : V) : degree ((Polynomial.X: F[X]) • C F v) ≤ 1 := by
  simpa only [pow_one] using degree_X_pow_smul_C_le 1 v

@[simp]
theorem natDegree_X_pow_smul_C (n : ℕ) (v : V) (hv : v ≠ 0) : natDegree ((Polynomial.X ^n : F[X]) • C F v)
   = n :=  natDegree_eq_of_degree_eq_some (degree_X_pow_smul_C F n hv)

@[simp]
theorem natDegree_X_smul_C (v : V) (hv : v ≠ 0) : natDegree ((Polynomial.X: F[X]) • C F v) = 1 := by
  simpa only [pow_one] using natDegree_X_pow_smul_C 1 v hv

@[simp]
theorem natDegree_single [DecidableEq V] (i : ℕ) (u : V) :
    natDegree (single F i u) = if u = 0 then 0 else i := by
  split_ifs with hu
  · simp [hu]
  · rw [← X_pow_smul_C_eq_single, natDegree_X_pow_smul_C i u hu]

theorem natDegree_single_le (v : V) {m : ℕ} : (single F m v).natDegree ≤ m := by
  classical
  rw [natDegree_single]
  split_ifs
  exacts [Nat.zero_le _, le_rfl]

theorem natDegree_single_eq (i : ℕ) {u : V} (u0 : u ≠ 0) : (single F i u).natDegree = i :=
  letI := Classical.decEq V
  Eq.trans (natDegree_single _ _) (if_neg u0)

theorem coeff_ne_zero_of_eq_degree (hn : degree vp = n) : vp n ≠ 0 := fun h =>
  mem_support_iff.mp (mem_of_max hn) h

theorem withBotSucc_degree_eq_natDegree_add_one (h : vp ≠ 0) : vp.degree.succ = vp.natDegree + 1 := by
  rw [degree_eq_natDegree h]
  exact WithBot.succ_coe vp.natDegree

@[simp]
theorem degree_neg (vp : (PolynomialModule F V)) : degree (-vp) = degree vp := by unfold degree; rw [support_neg]

theorem degree_neg_le_of_le {v : WithBot ℕ} {vp : (PolynomialModule F V)} (hv : degree vp ≤ v) : degree (-vp) ≤ v :=
  vp.degree_neg.le.trans hv

@[simp]
theorem natDegree_neg (vp : (PolynomialModule F V)) : natDegree (-vp) = natDegree vp := by simp [natDegree]

theorem natDegree_neg_le_of_le {vp : (PolynomialModule F V)} (hv : natDegree vp ≤ m) : natDegree (-vp) ≤ m :=
  (natDegree_neg vp).le.trans hv

@[simp]
theorem leadingCoeff_neg (vp : (PolynomialModule F V)) : (-vp).leadingCoeff = -vp.leadingCoeff := by
  rw [leadingCoeff, leadingCoeff, natDegree_neg]
  rfl

/-- The second-highest coefficient, or 0 for constants -/
def nextCoeff (vp : (PolynomialModule F V)) : V :=
  if vp.natDegree = 0 then 0 else vp (vp.natDegree - 1)

lemma nextCoeff_eq_zero :
    vp.nextCoeff = 0 ↔ vp.natDegree = 0 ∨ 0 < vp.natDegree ∧ vp (vp.natDegree - 1) = 0 := by
  simp [nextCoeff, or_iff_not_imp_left, pos_iff_ne_zero]; aesop

lemma nextCoeff_ne_zero : vp.nextCoeff ≠ 0 ↔ vp.natDegree ≠ 0 ∧ vp (vp.natDegree - 1) ≠ 0 := by
  simp [nextCoeff]

@[simp]
theorem nextCoeff_C_eq_zero (v : V) : nextCoeff (C F v) = 0 := by
  rw [nextCoeff]
  simp

theorem nextCoeff_of_natDegree_pos (hv : 0 < vp.natDegree) :
    nextCoeff vp = vp (vp.natDegree - 1) := by
  rw [nextCoeff, if_neg]
  contrapose! hv
  simpa

#check AddMonoidAlgebra.sup_support_add_le
#check Polynomial.support_toFinsupp
#check Polynomial.toFinsupp_add
theorem degree_add_le (vp wp : (PolynomialModule F V)) : degree (vp + wp) ≤ max (degree vp) (degree wp) := by
  -- simpa only [degree, ← support_toFinsupp, toFinsupp_add]
  --   using AddMonoidAlgebra.sup_support_add_le _ _ _
  sorry

theorem degree_add_le_of_degree_le {vp wp : (PolynomialModule F V)} {n : ℕ} (hv : degree vp ≤ n) (hw : degree wp ≤ n) :
    degree (vp + wp) ≤ n :=
  (degree_add_le vp wp).trans <| max_le hv hw

theorem degree_add_le_of_le {a b : WithBot ℕ} (hv : degree vp ≤ a) (hw : degree wp ≤ b) :
    degree (vp + wp) ≤ max a b :=
  (vp.degree_add_le wp).trans <| max_le_max ‹_› ‹_›

theorem natDegree_add_le (vp wp : (PolynomialModule F V)) : natDegree (vp + wp) ≤ max (natDegree vp) (natDegree wp) := by
  rcases le_max_iff.1 (degree_add_le vp wp) with h | h <;> simp [natDegree_le_natDegree h]


theorem natDegree_add_le_of_degree_le {vp wp : (PolynomialModule F V)} {n : ℕ} (hv : natDegree vp ≤ n)
    (hw : natDegree wp ≤ n) : natDegree (vp + wp) ≤ n :=
  (natDegree_add_le vp wp).trans <| max_le hv hw

theorem natDegree_add_le_of_le (hv : natDegree vp ≤ m) (hw : natDegree wp ≤ n) :
    natDegree (vp + wp) ≤ max m n :=
  (vp.natDegree_add_le wp).trans <| max_le_max ‹_› ‹_›

@[simp]
theorem leadingCoeff_zero : leadingCoeff (0 : (PolynomialModule F V)) = 0 :=
  rfl

@[simp]
theorem leadingCoeff_eq_zero : leadingCoeff vp = 0 ↔ vp = 0 :=
  ⟨fun h =>
    Classical.by_contradiction fun hv =>
      mt mem_support_iff.1 (Classical.not_not.2 h) (mem_of_max (degree_eq_natDegree hv)),
    fun h => h.symm ▸ leadingCoeff_zero⟩

theorem leadingCoeff_ne_zero : leadingCoeff vp ≠ 0 ↔ vp ≠ 0 := by rw [Ne, leadingCoeff_eq_zero]

theorem leadingCoeff_eq_zero_iff_deg_eq_bot : leadingCoeff vp = 0 ↔ degree vp = ⊥ := by
  rw [leadingCoeff_eq_zero, degree_eq_bot]

theorem natDegree_X_pow_smul_C_le (v : V) (n : ℕ) : natDegree ((Polynomial.X^n : F[X]) • C F v) ≤ n :=
  natDegree_le_iff_degree_le.2 <| degree_X_pow_smul_C_le _ _

/-- `erase vp n` is the polynomial vector `vp` in which the `X^n` term has been erased. -/
irreducible_def erase (n : ℕ) : PolynomialModule F V → PolynomialModule F V
  | vp => vp.erase n

@[simp]
theorem toFinsupp_erase (v : PolynomialModule F V) (n : ℕ) : v.erase n = (v: Finsupp ℕ V).erase n := by
  rcases v with ⟨⟩
  simp only [erase_def]

@[simp]
theorem support_erase (v : PolynomialModule F V) (n : ℕ) : support (v.erase n) = (support v).erase n := by
  rcases v with ⟨⟩
  simp only [support, erase_def, Finsupp.support_erase]


theorem degree_erase_le (vp : (PolynomialModule F V)) (n : ℕ) : degree (vp.erase n) ≤ degree vp := by
  rcases vp with ⟨vp⟩
  simp only [erase_def, degree, support]
  apply sup_mono
  rw [Finsupp.support_erase]
  apply Finset.erase_subset

theorem degree_erase_lt (hv : vp ≠ 0) : degree (vp.erase (natDegree vp)) < degree vp := by
  apply lt_of_le_of_ne (degree_erase_le _ _)
  rw [degree_eq_natDegree hv, degree, support_erase]
  exact fun h => notMem_erase _ _ (mem_of_max h)

/-- Replace the coefficient of a `pv : PolynomialModule F V` at a given degree `n : ℕ`
by a given value `v : V`. If `v = 0`, this is equal to `vp.erase n`
If `vp.natDegree < n` and `v ≠ 0`, this increases the degree to `n`. -/
abbrev update (vp : PolynomialModule F V) (n : ℕ) (v : V) : PolynomialModule F V :=
  (Finsupp.update (vp: Finsupp ℕ V) n v)


theorem degree_update_le (vp : (PolynomialModule F V)) (n : ℕ) (v : V) : degree (vp.update n v) ≤ max (degree vp) n := by
  classical
  rw [degree, support_update]
  split_ifs
  · exact (Finset.max_mono (erase_subset _ _)).trans (le_max_left _ _)
  · rw [max_insert, max_comm]
    exact le_rfl

theorem degree_sum_le (s : Finset ι) (f : ι → (PolynomialModule F V)) :
    degree (∑ i ∈ s, f i) ≤ s.sup fun b => degree (f b) :=
  Finset.cons_induction_on s (by simp only [sum_empty, sup_empty, degree_zero, le_refl])
    fun v s has ih =>
    calc
      degree (∑ i ∈ cons v s has, f i) ≤ max (degree (f v)) (degree (∑ i ∈ s, f i)) := by
        rw [Finset.sum_cons]; exact degree_add_le _ _
      _ ≤ _ := by rw [sup_cons]; exact max_le_max le_rfl ih



theorem natDegree_lt_natDegree {wp : PolynomialModule F V} (hp : vp ≠ 0) (hpq : vp.degree < wp.degree) :
    vp.natDegree < wp.natDegree := by
  by_cases hq : wp = 0
  · exact (not_lt_bot <| hq ▸ hpq).elim
  rwa [degree_eq_natDegree hp, degree_eq_natDegree hq, Nat.cast_lt] at hpq


@[elab_as_elim]
theorem induction_on_max_particular {motive : PolynomialModule F V → Prop} (f : PolynomialModule F V)
    (zero : motive 0) (add : ∀ f g, f ≠ 0 → g ≠ 0 → f.natDegree < g.natDegree → motive f → motive g → motive (f + g))
    (single : ∀ a b, b ≠ 0 → motive (single F a b)) : motive f := by
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


theorem natDegree_eq_zero_iff_degree_le_zero : vp.natDegree = 0 ↔ vp.degree ≤ 0 := by
  rw [← nonpos_iff_eq_zero, natDegree_le_iff_degree_le, Nat.cast_zero]

theorem degree_zero_le : degree (0 : (PolynomialModule F V)) ≤ 0 := natDegree_eq_zero_iff_degree_le_zero.mp rfl

theorem degree_le_iff_coeff_zero (vp : (PolynomialModule F V)) (n : WithBot ℕ) :
    degree vp ≤ n ↔ ∀ m : ℕ, n < m → vp m = 0 := by
  simp only [degree, Finset.max, Finset.sup_le_iff, mem_support_iff, Ne, ← not_le,
    not_imp_comm, Nat.cast_withBot]

theorem degree_lt_iff_coeff_zero (vp : (PolynomialModule F V)) (n : ℕ) :
    degree vp < n ↔ ∀ m : ℕ, n ≤ m → vp m = 0 := by
  simp only [degree, Finset.sup_lt_iff (WithBot.bot_lt_coe n), mem_support_iff,
    WithBot.coe_lt_coe, ← @not_le ℕ, max_eq_sup_coe, Nat.cast_withBot, Ne, not_imp_not]

theorem natDegree_pos_iff_degree_pos : 0 < natDegree vp ↔ 0 < degree vp :=
  lt_iff_lt_of_le_iff_le natDegree_le_iff_degree_le

example (a b: V): a-b=a+-b := by
  exact sub_eq_add_neg a b

theorem degree_sub_le (vp wp : (PolynomialModule F V)) : degree (vp - wp) ≤ max (degree vp) (degree wp) := by
  rw[sub_eq_add_neg, <- degree_neg wp]
  exact degree_add_le vp (-wp)

theorem degree_sub_le_of_le {a b : WithBot ℕ} (hv : degree vp ≤ a) (hw : degree wp ≤ b) :
    degree (vp - wp) ≤ max a b :=
  (vp.degree_sub_le wp).trans <| max_le_max ‹_› ‹_›

theorem natDegree_sub_le (vp wp : (PolynomialModule F V)) : natDegree (vp - wp) ≤ max (natDegree vp) (natDegree wp) := by
  rw[sub_eq_add_neg, <- natDegree_neg wp]
  exact natDegree_add_le vp (-wp)

theorem natDegree_sub_le_of_le (hv : natDegree vp ≤ m) (hw : natDegree wp ≤ n) :
    natDegree (vp - wp) ≤ max m n :=
  (vp.natDegree_sub_le wp).trans <| max_le_max ‹_› ‹_›

theorem single_add_erase (vp : PolynomialModule F V) (n : ℕ) : single F n (vp n) + vp.erase n = vp := by
  apply Finsupp.ext
  intro i
  by_cases hin: n=i
  . rw[hin, add_apply, single_apply, erase_def]
    simp
  . rw[add_apply, single_apply]
    simp only [hin, ↓reduceIte, zero_add]
    rw[erase_def]
    exact erase_ne fun a ↦ hin (id (Eq.symm a))

theorem degree_sub_lt (hd : degree vp = degree wp) (hp0 : vp ≠ 0)
    (hlc : leadingCoeff vp = leadingCoeff wp) : degree (vp - wp) < degree vp :=
  have hv : single F (natDegree vp) (leadingCoeff vp) + vp.erase (natDegree vp) = vp :=
    single_add_erase _ _
  have hw : single F (natDegree wp) (leadingCoeff wp) + wp.erase (natDegree wp) = wp :=
    single_add_erase _ _
  have hd' : natDegree vp = natDegree wp := by unfold natDegree; rw [hd]
  have hw0 : wp ≠ 0 := mt degree_eq_bot.2 (hd ▸ mt degree_eq_bot.1 hp0)
  calc
    degree (vp - wp) = degree (erase (natDegree wp) vp + -erase (natDegree wp) wp) := by
      conv =>
        lhs
        rw [← hv, ← hw, hlc, hd', add_sub_add_left_eq_sub, sub_eq_add_neg]
    _ ≤ max (degree (erase (natDegree wp) vp)) (degree (erase (natDegree wp) wp)) :=
      (degree_neg (erase (natDegree wp) wp) ▸ degree_add_le _ _)
    _ < degree vp := max_lt_iff.2 ⟨hd' ▸ degree_erase_lt hp0, hd.symm ▸ degree_erase_lt hw0⟩

theorem degree_eq_degree_if_natDegree_eq_natDegree (hd : natDegree vp = natDegree wp) (hv : vp ≠ 0)
 (hw : wp ≠ 0): degree vp = degree wp := by
  rw[degree_eq_natDegree hv, degree_eq_natDegree hw, hd]

theorem natDegree_sub_lt (hd : natDegree vp = natDegree wp) (hw : wp ≠ 0) (hv_deg: natDegree vp>0)
    (hlc : leadingCoeff vp = leadingCoeff wp) : natDegree (vp - wp) < natDegree vp := by
  have hv: vp ≠ 0 := by
    have: vp.natDegree ≠ 0 := by exact Nat.ne_zero_of_lt hv_deg
    exact Ne.symm (ne_of_apply_ne natDegree fun a ↦ this (id (Eq.symm a)))
  have hd : degree vp = degree wp := degree_eq_degree_if_natDegree_eq_natDegree hd hv hw
  by_cases h: vp=wp
  . nth_rewrite 1[h]
    simp only [sub_self, natDegree_zero]
    apply hv_deg
  . rw[natDegree_lt_iff_degree_lt]
    rw[<- degree_eq_natDegree]
    . exact degree_sub_lt hd hv hlc
    . exact hv
    . intro h'
      have: vp=wp := by
        rw[<- add_zero wp, <- h', add_comm, sub_add,sub_self, sub_zero]
      exact h this

end PolynomialModule
