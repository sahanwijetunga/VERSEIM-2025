--------------------------------------------------------------------------------
/-
Copyright (c) 2025 George McNinch. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Author : George McNinch
-/

/- VERSEIM-2025 REU -/

import Mathlib.Tactic

-- indexed union/intersection of sets

-- given types α and I, a function `I → Set α`
-- describes a family of `Set α`s indexed by the type `I`

-- for example, a sequence of sets `A₀, A₁, ...` (really: of `Set α`s)
-- is determined by a function `ℕ → set β`

example (α:Type) (A : ℕ → Set α) : Set α := by
  exact ⋃ i, A i


