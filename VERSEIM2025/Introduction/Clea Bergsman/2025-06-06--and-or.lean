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

-- alternatively, you can use the same anonymous constructor notation
-- to produce terms involving ands

example (p q : Prop) : p ∧ q → q ∧ p := by
  intro ⟨x,y⟩
  exact ⟨y,x⟩

--------------------------------------------------------------------------------

-- you can "pattern match" via a `have`

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  have ⟨h₀, h₁⟩ := h
  contrapose! h₁
  exact le_antisymm h₀ h₁

--------------------------------------------------------------------------------

-- iff

-- In Lean, A ↔ B is not defined to be (A → B) ∧ (B → A), but it could have been, and it behaves roughly the same way.

-- can use `constructor` when proving an iff statement, just like for an `∧`

-- mp stands for `modus ponens` and mpr for `modus ponens reverse`
-- these are the names of the goals after using `constructor` in the following:

def iff_symm { P Q : Prop } (h: P ↔ Q) : (Q ↔ P) := by
  exact ⟨ h.mpr, h.mp ⟩

example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor
  · intro hf; exact iff_symm hf
  · intro hr; exact iff_symm hr


example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro ⟨h0,h1⟩
  intro ⟨ x, y⟩
  constructor
  intro p
  exact x (h0 (h1 (h0 p)))
  intro r
  exact h1 (h0 (h1 (y r)))



example {x y : ℝ} (h : x ≤ y) : ¬y ≤ x ↔ x ≠ y := by
  constructor
  · contrapose!
    rintro rfl
    rfl
  · contrapose!
    exact le_antisymm h

example {x y : ℝ} (h : x ≤ y) : ¬y ≤ x ↔ x ≠ y :=
  ⟨fun h₀ h₁ ↦ h₀ (by rw [h₁]), fun h₀ h₁ ↦ h₀ (le_antisymm h h₁)⟩

--------------------------------------------------------------------------------


example (p q : Prop) : p → p ∨ q := by
  intro x
  exact Or.inl x
