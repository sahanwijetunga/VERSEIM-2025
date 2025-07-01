--------------------------------------------------------------------------------
/-
Copyright (c) 2025 Clea Bergsman, Katherine Buesing, George McNinch, Sahan Wijetunga. All rights reserved.

Released under the Apache 2.0 license as described in the file LICENSE.

VERSEIM-2025 REU @ Tufts University
-/

import Mathlib.Tactic


variable { k V : Type } [Field k] [ AddCommGroup V ]  [Module k V]

variable (β:V →ₗ[k] V →ₗ[k] k)

def Alt (β:V →ₗ[k] V →ₗ[k] k) : Prop :=
  ∀ v : V, β v v = 0

def Skew (β:V →ₗ[k] V →ₗ[k] k) : Prop :=
  ∀ v w : V, β v w = -β w v

def Symm (β:V →ₗ[k] V →ₗ[k] k) : Prop :=
  ∀ v w : V, β v w = β w v


lemma skew_of_alt (β:V →ₗ[k] V →ₗ[k] k) (ha : Alt β) :
  Skew β := by
  intro v w
  have h0 : β (v+w) = β v + β w := by simp
  have h : β (v+w) (v+w) = (β v) v + (β w) v + (β v) w + (β w) w :=
    calc
    (β (v+w)) (v+w) = (β v) (v+w) + (β w) (v+w) := by rw [LinearMap.BilinForm.add_left]
    _ = (β v) v + (β w) v + (β v) w + (β w) w := by
      rw [LinearMap.BilinForm.add_right v v w, LinearMap.BilinForm.add_right w v w, ← add_assoc]; ring
  have hv : β v v = 0 := by apply ha
  have hw : β w w = 0 := by apply ha
  have hvw : β (v+w) (v+w) = 0 := by apply ha
  rw [hv, hw, hvw, zero_add, add_zero, add_comm] at h
  have h1: 0 + -(β w) v = (β v) w + (β w) v + -(β w) v := by
    apply (@add_right_cancel_iff _ _ _ (-(β w) v) 0 ((β v) w + (β w) v)).mpr h
  rw [zero_add] at h1
  rw [← sub_eq_add_neg] at h1
  rw [← add_sub ((β v) w) ((β w) v) ((β w) v)] at h1
  rw [sub_self ((β w) v)] at h1
  rw [add_zero] at h1
  symm at h1
  exact h1

--have h1 : (β v) w = -(β w) v := by exact Eq.symm (LinearMap.BilinForm.IsAlt.neg_eq ha w v)
 -- symm at h
  --rw [add_comm] at h
 -- rw [← add_eq_zero_iff_eq_neg'.mp] at h

#check add_assoc
#check add_eq_zero_iff_eq_neg'
#check sub_self
#check congr_arg
#check LinearMap.map_add
#check LinearMap.BilinForm.add_left
#check LinearMap.BilinForm.add_right
#check add_right_cancel_iff
#check sub_eq_add_neg


example (β : V →ₗ[k] V →ₗ[k] k)  (v w x : V) : β (v + w) x = β v x + β w x := by
  have h : β (v + w) = β v + β w := by simp
  rw [h]
  rfl

lemma eq_zero_of_two_mul_eq_zero { k V : Type } [ Field k] [ AddCommGroup V]
  [Module k V] {p:ℕ} [CharP k p] (hn2 : p ≠ 2)
  (v:V) (h:2•v = 0) : v = 0 := by
    have two_smul_eq_zero : (2:k) • v = 0 := by
      rw [ ofNat_smul_eq_nsmul k 2 v ]
      assumption
    have ring_char_n2 : ringChar k ≠ 2 := by
       rw [ ringChar.eq k p ]
       assumption
    have two_neq_zero : (2:k) ≠ 0 := by
       apply Ring.two_ne_zero ring_char_n2
    by_contra v_neq_zero
    have two_smul_ne_zero : (↑2:k) • v ≠ 0 :=
       smul_ne_zero two_neq_zero v_neq_zero
    exact two_smul_ne_zero two_smul_eq_zero

lemma zero_of_two_mul_eq_zero  { k : Type } [ Field k]
  [CharZero k] (x:k) (h:2*x = 0) : x = 0 := by
  --have nz2_inst : NeZero ↑2 := inferInstance
  have nz2 : (2:k) ≠ 0 := NeZero.ne ↑2
  by_contra x_neq_zero
  have two_mul_ne_zero : ↑2*x ≠ 0 :=
    mul_ne_zero nz2 x_neq_zero
  exact two_mul_ne_zero h

lemma alt_iff_skew (β:V →ₗ[k] V →ₗ[k] k)
   [CharP k p] (hn2 : p ≠ 2)
   : Alt β ↔ Skew β := by
   constructor
   intro ha
   apply skew_of_alt
   exact ha
   intro hs
   intro v
   have h1 : β v v = -β v v := by apply hs
   have h2 : β v v + β v v = β v v + -β v v := by
     apply (@add_left_cancel_iff _ _ _ (β v v) (β v v) (-β v v)).mpr  h1
   rw [← sub_eq_add_neg, sub_self ((β v) v)] at h2
   rw [← two_mul] at h2
   apply zero_of_two_mul_eq_zero at h2
   exact h2

#check CharZero k


-- REMARK: we are really only interested in the case of forms which
-- are either alternating or symmetric.  We are going to formulate a
-- number of predicates on forms which in the general case (of a form
-- which is neither alternating nor symmetric) should have a more
-- complicated definition.


def OrthogSubspaces (β:V →ₗ[k] V →ₗ[k] k) (W₁ W₂ : Submodule k V) : Prop :=
  ∀ (x:W₁), ∀ (y:W₂), β x y = 0

def fun_is_orthog (β:V →ₗ[k] V →ₗ[k] k) {n:ℕ} (vect : Fin n → V) : Prop :=
  ∀ i j : Fin n, i ≠ j → β (vect i) (vect j) = 0

theorem lin_indep_of_orthog (β:V →ₗ[k] V →ₗ[k] k) (f : Fin n → V) :  LinearIndependent k f := by sorry


-- predicate for orthogonality of sets
def OrthogSets  (β:V →ₗ[k] V →ₗ[k] k) (s₁ s₂ : Set V) : Prop :=
  ∀ x₁ ∈ s₁, ∀ x₂ ∈ s₂, β x₁ x₂ = 0


lemma orthog_sets_iff_orthog_subspaces (β:V →ₗ[k] V →ₗ[k] k) (s₁ s₂ : Set V) :
  OrthogSets β s₁ s₂ ↔ OrthogSubspaces β (Submodule.span k s₁) (Submodule.span k s₂) := by sorry
