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

example (a: two_simplex) two_simplex where
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
  sum_eq_one : (∑ i, V i) = 1

#check Fin

variable (α β γ : Type)

#check Equiv α β
#check α  ≃ β

#check Function.RightInverse

structure Group₁ (α : Type*) where
  mul : α → α → α
  one : α
  inv : α → α
  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  mul_one : ∀ x : α, mul x one = x
  one_mul : ∀ x : α, mul one x = x
  inv_mul_cancel : ∀ x : α, mul (inv x) x = one

example (α :Type) (G:Group₁ α) : ∀ x : α, G.mul x x = x → x = G.one := by
  intro x h
  let y : α := G.inv x
  have k : G.mul y (G.mul x x) = G.mul y x :=  congrArg (fun t => G.mul y t) h
  rw [←G.mul_assoc y x x] at k
  unfold y at k
  rw [G.inv_mul_cancel x] at k
  rw [G.one_mul] at k
  assumption

class MyDisplay (α:Type) where
  mydisp : α → String

instance : MyDisplay two_simplex  where
  mydisp a := "< x:" ++ reprStr a.x ++ ", y:" ++ reprStr a.y ++ ", z:" ++ reprStr a.z ++ " >"

def doubleString {α : Type} [MyDisplay α] (a : α) : String := by
  open MyDisplay in
  exact mydisp a ++ mydisp a

  ---------------------------------------------------------------------
  -- group as a typeclass rather than a structure

  variable(G: Type) [Group G]
  example (x y : G) : G := Mul.mul x y

  variable(A : Type) [AddGroup A]

  example (a b c : A) : a + b + c = a  + (b + c) := by
    rw[add_assoc]
