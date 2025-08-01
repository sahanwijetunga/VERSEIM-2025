--------------------------------------------------------------------------------
/-
Copyright (c) 2025 George McNinch. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Clea Bergsman, Katherine Buesing, George McNinch, Sahan Wijetunga
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
   | dow.Mon => "Mon"
   | dow.Tue => "Tue"
   | dow.Wed => "Wed"
   | dow.Thu => "Thu"

#eval f dow.Mon

variable (α:Type)
variable (s t u : Set α) 

example (h:s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intro x xsu  
  sorry

#check Set.subset_def
#check Set.inter_def

#check Set.union_def

#check Set.mem_setOf

open Set

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
  sorry




