--------------------------------------------------------------------------------
/-
Copyright (c) 2025 George McNinch. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Author : George McNinch
-/

/- VERSEIM-2025 REU -/

import Mathlib.Tactic

-- how to "create a term of a "type involve ∧"

example (p q : Prop) : p → q → p ∧ q := by
  intro x y
  exact And.intro x y 


example (p q : Prop) : p → q → p ∧ q :=  
  fun x y => And.intro x y


example (p q : Prop) : p → q → p ∧ q := by
  intro x y
  constructor 
  · exact x
  · exact y

-- the `constructor` tactic allows us to produce a term of type `p ∧ q` by first
-- giving a term of type p and then giving a term of type q

-- here it is "hiding" the need to know the name of `And.intro`

example (p q : Prop) : p ∧ q → q ∧ p := by
  intro ⟨x,y⟩
  constructor
  · exact y
  · exact x

--------------------------------------------------------------------------------

-- 


example (p q : Prop) : p → p ∨ q := by
  intro x
  exact Or.inl x

