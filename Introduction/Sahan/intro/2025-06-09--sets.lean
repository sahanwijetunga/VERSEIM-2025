--------------------------------------------------------------------------------
/-
Copyright (c) 2025 George McNinch. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Author : George McNinch
-/

/- VERSEIM-2025 REU -/

import Mathlib.Tactic

inductive dow
 | Mon
 | Tue
 | Wed
 | Thu

def f : dow → String :=
  fun d => match d with
   | dow.Mon => "aMon"
   | dow.Tue => "aTue"
   | dow.Wed => "aWed"
   | dow.Thu => "aThu"

#eval f dow.Mon

inductive option' (α: Type)
| none
| some (a: α)

inductive list' (α: Type)
| nil
| cons : α → list' α → list' α

def x: Set Prop := {True, True, 1=0}

variable (α:Type)
variable (s t u : Set α)

example (h:s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intro x ⟨hs, hu⟩
  exact ⟨h hs, hu⟩

example (x: ℕ ): Set ℝ  := {(x: ℝ)}

#check (Set.univ : Set α)

#check Set.univ α

#check Set.subset_def
#check Set.inter_def

#check Set.union_def

#check Set.mem_setOf

open Set

example (x: α) : Prop := s x

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def, inter_def, inter_def]
  rw [subset_def] at h
  --simp
  simp only [mem_setOf]
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  simp only [subset_def, mem_inter_iff] at *
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intro x xsu
  exact ⟨h xsu.1, xsu.2⟩


-- exercise: try this one (find it in math-in-lean and look at the preceding examples

example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  rintro x (⟨hs, ht⟩ | ⟨hs, hu⟩)
  . exact ⟨hs, Or.inl ht⟩
  . exact ⟨hs, Or.inr hu⟩

example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  rintro x h
  rcases h with ⟨hs, ht⟩ | ⟨hs, hu⟩
  . exact ⟨hs, Or.inl ht⟩
  . exact ⟨hs, Or.inr hu⟩


-- example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) :=
--   fun x ⟨hs, ht⟩ => sorry | ⟨hs, hu⟩ => sorry)

--------

example (x: ℝ): Even x :=  by
  use x/2
  ring

def evens : Set ℕ :=
  { n | Even n }

def odds : Set ℕ :=
  { n | ¬Even n }

example : evens ∪ odds = univ := by
  rw [evens, odds]
  ext n
  simp [-Nat.not_even_iff_odd]
  exact Classical.em _
