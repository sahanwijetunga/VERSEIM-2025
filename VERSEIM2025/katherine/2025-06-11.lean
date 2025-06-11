--------------------------------------------------------------------------------
/-
Copyright (c) 2025 George McNinch. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Author : George McNinch
-/

/- VERSEIM-2025 REU -/

import Mathlib.Tactic

structure two_simplex where
  x : ℝ
  y : ℝ
  z : ℝ
  sum_to_one : x + y + z = 1
  x_nonneg : 0 ≤ x
  y_nonneg : 0 ≤ y
  z_nonneg : 0 ≤ z

example : two_simplex where
  x := 1
  y := 0
  z := 0
  x_nonneg := by linarith
  y_nonneg := by linarith
  z_nonneg := by linarith
  sum_to_one := by ring

  def swapXy (a : two_simplex) : two_simplex
      where
  x := a.y
  y := a.x
  z := a.z
  x_nonneg := a.y_nonneg
  y_nonneg := a.x_nonneg
  z_nonneg := a.z_nonneg
  sum_to_one := by rw[add_comm a.y a.x, a.sum_to_one]

--open BigOperators

structure StandardSimplex (n : ℕ) where
  V: Fin n → ℝ
  NonNeg: ∀ i: Fin n, 0 ≤ V i
  sum_eq_one : (∑i, Vi) = 1

#check Fin

variable (α β γ : Type)

#check Equiv α β
#check α  ≃ β

#check Function.RightInverse



example : Group₁ (α ≃ α) := by
  mul := Equiv.trans
