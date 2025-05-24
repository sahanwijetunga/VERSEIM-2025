/-
Copyright (c) 2024 George McNinch. All rights reserved.
Released under the MIT license as described in the file LICENSE.
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
  sorry

-- 2
example : A ∪ A = A := by 
  sorry

-- 3
example : g ∘ f ⁻¹' C = f ⁻¹' (g ⁻¹' C) := by 
  sorry
  
