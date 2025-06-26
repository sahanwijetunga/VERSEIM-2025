/-
Copyright (c) 2024 George McNinch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : George McNinch
-/

/-
course: Math 190 - Tufts University
instructor: George McNinch
semester: 2024 Spring
-/

import Mathlib.Tactic

--------------------------------------------------------------------------------
-- 05 -- Sets and subsets -- **Exercises**
--------------------------------------------------------------------------------

variable (α β γ: Type)

variable (f : α → β) (g : β → γ)

variable (A : Set α) (B : Set β) (C : Set γ)

variable (X Y Z : Set α)

#check g ∘ f -- function composition; has type `α → γ`

open Set

-- 1
example : X ⊆ Y → X ⊆ Z → X ⊆ Y ∩ Z:= by
  intro hxy hxz
  intro x hx
  constructor
  · exact hxy hx
  · exact hxz hx

-- 2
example : A ∪ A = A := by
  ext x

  constructor
  · intro h
    rcases h <;>
    · assumption
  . intro h
    left
    exact h

-- 3
example : g ∘ f ⁻¹' C = f ⁻¹' (g ⁻¹' C) := by
  rfl

example (x y z: ℤ) (h0: x ∣ y) (h1: y ∣ z) : x ∣ z := by
  -- calc
  --   x ∣ y := h0
  --   y ∣ z := h1
  rcases h0 with ⟨a, ha⟩
  rcases h1 with ⟨b, hb⟩
  rw[hb, ha]
  apply dvd_mul_of_dvd_left
  apply dvd_mul_right
