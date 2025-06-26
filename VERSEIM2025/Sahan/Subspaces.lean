
--------------------------------------------------------------------------------
/-
Copyright (c) 2025 Clea Bergsman, Katherine Buesing, George McNinch, Sahan Wijetunga. All rights reserved.

Released under the Apache 2.0 license as described in the file LICENSE.

VERSEIM-2025 REU VERSEIM-2025 REU @ Tufts University
-/

import Mathlib.Tactic
import VERSEIM2025.Sahan.BilinearForms

--------------------------------------------------------------------------------
def disjointUnion_funs {ι κ X: Type} ( f₁:ι → X) (f₂:κ → X) (u: ι ⊕ κ) : X :=
   match u with
    | Sum.inl x => f₁ x
    | Sum.inr y => f₂ y

def fun1 (m n: ℕ): (Fin n) ⊕ (Fin m) → Fin (n+m) :=
   fun i =>
    match i with
    | Sum.inl x => Fin.castAdd m x
    | Sum.inr ⟨x, h⟩  => by
        rw [ add_comm ]
        exact ⟨x+n, Nat.add_lt_add_right h n⟩

@[simp]
lemma fun1_left (m n: ℕ) (i: Fin n): fun1 m n (Sum.inl i) = Fin.castAdd m i := by
   simp[fun1]

@[simp]
lemma fun1_right (m n: ℕ) (j: Fin m): fun1 m n (Sum.inr j) = Fin.natAdd n j := by
   have ⟨j, h⟩ := j
   simp
   refine cast_eq_iff_heq.mpr ?_
   refine (Fin.heq_ext_iff ?_).mpr ?_
   . exact Nat.add_comm m n
   exact Nat.add_comm j n

def reverse_ineq {n m i: ℕ} (h: i<m+n) : i<n+m := by
   rw[add_comm]
   exact h

def fun2 (m n: ℕ): Fin (n+m) → (Fin n) ⊕ (Fin m) :=
   fun ⟨i,hi⟩ =>
   if h : i < n then
      Sum.inl (⟨↑i, h⟩: Fin n)
   else
      Sum.inr (Fin.subNat n (⟨i,reverse_ineq hi⟩: Fin (m+n)) (Nat.le_of_not_lt h))


@[simp]
lemma fun2_less (m n: ℕ) (i: Fin (n+m)) (h: ↑i< n): fun2 m n i = Sum.inl (⟨↑i, h⟩: Fin n) := by
   simp_all[fun2]

@[simp]
lemma fun2_more (m n: ℕ) (i: Fin (n+m)) (h: ↑i≥ n): fun2 m n i =
   Sum.inr (Fin.subNat n (⟨(↑i: ℕ),reverse_ineq i.is_lt⟩: Fin (m+n)) h) := by
   have: ¬ ↑i< n := by exact Nat.not_lt.mpr h
   simp[fun2,this]


def fin_disjoint_fin_equiv_fin (n m: ℕ) : (Fin n) ⊕ (Fin m) ≃ Fin (n+m) where
  toFun := fun1 m n
  invFun := fun2 m n
  left_inv := by
   intro a
   match a with
   | Sum.inl i => simp
   | Sum.inr j => simp_all

  right_inv := by
      intro a
      by_cases h:(a<n)
      .  simp_all
      .  simp_all

theorem lin_indep_by_transverse_subspaces
   (k V : Type) [Field k] [AddCommGroup V] [Module k V] (I₁ I₂ : Type)
   (b₁ : I₁ → V) (b₂ : I₂ → V)
   (b1_indep : LinearIndependent k b₁)
   (b2_indep : LinearIndependent k b₂)
   (W₁ W₂ : Submodule k V)
   (h_int : W₁ ⊓ W₂ = ⊥)
   (hbw1 : ∀ i, b₁ i ∈ W₁)
   (hbw2 : ∀ i, b₂ i ∈ W₂)
   : LinearIndependent k (disjointUnion_funs b₁ b₂) := by
      rw[linearIndependent_sum]
      constructor
      .  exact b1_indep
      constructor
      . exact b2_indep
      show Disjoint (Submodule.span k (Set.range b₁)) (Submodule.span k (Set.range b₂))
      have h1: Submodule.span k (Set.range b₁) ≤ W₁ := by
         suffices Set.range (b₁) ⊆ W₁ from ?_
         . exact Submodule.span_le.mpr this
         exact Set.range_subset_iff.mpr hbw1
      have h2: Submodule.span k (Set.range b₂) ≤ W₂ := by
         suffices Set.range (b₂) ⊆ W₂ from ?_
         . exact Submodule.span_le.mpr this
         exact Set.range_subset_iff.mpr hbw2
      have hw: Disjoint W₁ W₂ := by exact disjoint_iff.mpr h_int
      exact Disjoint.mono h1 h2 hw




--------------------------------------------------------------------------------
