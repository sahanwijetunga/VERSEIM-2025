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
  ∀ v w : V, β v w = - β w v

def Symm (β:V →ₗ[k] V →ₗ[k] k) : Prop :=
  ∀ v w : V, β v w = β w v

lemma skew_of_alt (β:V →ₗ[k] V →ₗ[k] k) (ha : Alt β) :
  Skew β := by
  intro v w
  suffices β v w + β w v = 0 from ?_
  . exact Eq.symm (LinearMap.BilinForm.IsAlt.neg_eq ha w v)
  calc
    β v w + β w v = β v w+ β w v + β v v + β w w := by
      rw[ha v, ha w]
      abel
    _ = β (v+w) (v+w) := by
      simp
      abel
    _ = 0 := ha _

lemma div_2 {p} (hp: CharP k p) (hn2 : p ≠ 2) (v: V) (h: v+v=0) : v=0 := by
  have : (2 : k) • v = 0 := by
    rw[<- h]
    exact two_smul k v
  -- Since char k ≠ 2, 2 ≠ 0 in k
  have h2 : (2 : k) ≠ 0 := by
    intro h
    have: CharP k 2 := by
      refine CharTwo.of_one_ne_zero_of_two_eq_zero ?_ h
      exact one_ne_zero
    simp_all
    have: 2=p := by exact CharP.eq k this hp
    exact hn2 this.symm
  -- Now cancel scalar multiplication by 2
  calc
    v = (1: k) • v := by exact Eq.symm (MulAction.one_smul v)
    _ = ((2: k)⁻¹ * (2: k) )• v :=  by
      suffices (2: k)⁻¹ * (2: k) = (1: k) from ?_
      . exact congrFun (congrArg HSMul.hSMul (id (Eq.symm this))) v
      exact inv_mul_cancel₀ h2
    _ = (2: k)⁻¹ • (2: k) • v := by exact mul_smul 2⁻¹ 2 v
    _ = 0 := by simp_all


lemma alt_iff_skew  {p}(β:V →ₗ[k] V →ₗ[k] k)
   (hp2: CharP k p) (hn2 : p ≠ 2)
   : Alt β ↔ Skew β := by
  constructor
  . intro h
    simp[Alt, Skew] at *
    intro v w
    suffices β v w + β w v = 0 from ?_
    . exact Eq.symm (LinearMap.BilinForm.IsAlt.neg_eq h w v)

    calc
      (β v) w + (β w) v = β v w + β w v + β v v + β w w := by
        simp_all
      _ = β (v+w) (v+w) := by simp_all
      _ = 0 := h (v+w)
  . intro h
    simp[Alt, Skew] at *
    intro v
    have: β v v = - β v v := h v v
    have: β v v + β v v = 0 := by exact eq_neg_iff_add_eq_zero.mp (h v v)
    exact div_2 hp2 hn2 (β v v) this


-- REMARK: we are really only interested in the case of forms which
-- are either alternating or symmetric.  We are going to formulate a
-- number of predicates on forms which in the general case (of a form
-- which is neither alternating nor symmetric) should have a more
-- complicated definition.


def OrthogSubspaces (β:V →ₗ[k] V →ₗ[k] k) (W₁ W₂ : Submodule k V) : Prop :=
  ∀ (x:W₁), ∀ (y:W₂), β x y = 0

def fun_is_orthog (β:V →ₗ[k] V →ₗ[k] k) {n:ℕ} (vect : Fin n → V) : Prop :=
  ∀ i j : Fin n, i ≠ j → β (vect i) (vect j) = 0

theorem lin_indep_of_orthog (β:V →ₗ[k] V →ₗ[k] k) (f : Fin n → V) :
 LinearIndependent k f := by sorry


-- predicate for orthogonality of sets
def OrthogSets  (β:V →ₗ[k] V →ₗ[k] k) (s₁ s₂ : Set V) : Prop :=
  ∀ x₁ ∈ s₁, ∀ x₂ ∈ s₂, β x₁ x₂ = 0

#check Submodule.closure_induction
#check Submodule.span_induction
#check Submodule.mem_span_iff_exists_finset_subset

lemma orthog_sets_iff_orthog_subspaces (β:V →ₗ[k] V →ₗ[k] k) (s₁ s₂ : Set V) :
  OrthogSets β s₁ s₂ ↔ OrthogSubspaces β (Submodule.span k s₁) (Submodule.span k s₂) := by
  constructor
  . intro h
    unfold OrthogSubspaces
    intro ⟨x, hx⟩  ⟨y, hy⟩
    rw[Submodule.mem_span_iff_exists_finset_subset] at hx
    rw[Submodule.mem_span_iff_exists_finset_subset] at hy
    simp
    have ⟨fx,tx, hstx, hsuppx, hx⟩ := hx
    have ⟨fy,ty, hsty, hsuppy, hy⟩ := hy
    rw[<- hx, <- hy]
    simp

    have (i j: V) (hx: i ∈ tx) (hy : j ∈ ty): β i j =0:= by
      exact h i (hstx hx) j (hsty hy)
    simp_all
  . intro h
    intro x hx y hy
    have hx: x ∈ Submodule.span k s₁ := by exact Submodule.mem_span.mpr fun p a ↦ a hx
    have hy: y ∈ Submodule.span k s₂ := by exact Submodule.mem_span.mpr fun p a ↦ a hy
    simp_all[OrthogSubspaces]
