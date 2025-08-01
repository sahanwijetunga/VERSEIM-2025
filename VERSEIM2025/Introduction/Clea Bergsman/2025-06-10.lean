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

#check Even
#check Prop

example: ({1}: Set ℕ ) = ({1, 1}: Set ℕ ):= by
  ext x
  simp

example (p q r : Prop) : p ∨ (q ∧ r) → q ∨ p := by
  intro h
  rcases h with hp | ⟨ hq, hr ⟩
  right
  exact hp
  left
  exact hq

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun _: ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nge
  dsimp
  rw [sub_self, abs_zero]
  apply εpos

@[ext]
structure complex where
  re : ℚ
  im : ℚ

example (a b : complex) (hr : a.re = b.re) (hi : a.im = b.im) : a = b := by
  ext
  repeat assumption

def add ( a b : complex) : complex where
 re := a.re + b.re
 im := a.im + b.im

def mul (a b : complex) : complex where
  re := a.re * b.re - a.im * b.im
  im := a.re * b.im + b.re * a.im

def conj (a : complex) : complex where
  re:= a.re
  im := -a.im

def norm_sq (a:complex) : ℚ :=
  (mul a (conj a)).re

-- Groups

structure mygroup where
  carrier : Type
  mul : carrier → carrier → carrier
  e : carrier

  identity_law_l : (g : carrier) → mul e g = g
  identity_law_r : (g : carrier) → mul g e = g

  assoc ( g h k : carrier) : mul (mul g h) k = mul g (mul h k)

  inverse_l (g: carrier) : ∃ h, mul g h = e
  inverse_r (g: carrier) : ∃ h, mul h g = e

structure two_simplex where
  x : ℝ
  y : ℝ
  z : ℝ
  x_nonneg : 0 ≤ x
  y_nonneg : 0 ≤ y
  z_nonneg : 0 ≤ z
  sum_to_one : x + y + z = 1

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
  sum_to_one := by rw [add_comm a.y a.x, a.sum_to_one]

open BigOperators

structure StandardSimplex (n : ℕ) where
  V : Fin n → ℝ
  NonNeg : ∀ i : Fin n, 0 ≤ V i
  sum_eq_one : (∑ i, V i) = 1


structure Group_1 (α : Type*)  where
  mul : α → α → α
  one : α
  inv : α → α
  mul_assoc : ∀ g h k : α, mul (mul g h) k = mul g (mul h k)
  mul_one : ∀ x : α, mul x one = x
  one_mul : ∀ x : α, mul one x = x
  inv_mul_cancel : ∀ x : α, mul (inv x) x = one

variable (α β γ : Type)

#check Equiv α β
#check α ≃ β

variable (f : α ≃ β)

#check f.toFun
#check f.invFun
#check Equiv.refl
#check f.right_inv
#check Function.RightInverse

def permGroup {α : Type*} : Group_1 (Equiv.Perm α)
    where
  mul f g := Equiv.trans g f
  one := Equiv.refl α
  inv := Equiv.symm
  mul_assoc f g h := (Equiv.trans_assoc _ _ _).symm
  one_mul := Equiv.trans_refl
  mul_one := Equiv.refl_trans
  inv_mul_cancel := Equiv.self_trans_symm

example (α : Type) (G : Group_1 α) : ∀ x : α, G.mul x x = x → x = G.one := by
  intro x h
  let y : α := G.inv x
  have k : G.mul y (G.mul x x) = G.mul y x := congrArg (fun t => G.mul y t) h
  rw [← G.mul_assoc y x x] at k
  unfold y at k
  rw [G.inv_mul_cancel x] at k
  rw [G.one_mul] at k
  exact k

instance : Inhabited two_simplex where
  default := by sorry
    --apply two_simplex.mk (1/3) (1/3) (1/3)
    --repeat linarith

variable (G:Type) [Group G]

#check Group

example ( x y : G) : G := x * y -- Mul.mul x y

example (x:G) : x*1 = x := by group

variable (A : Type) [AddGroup A]

example (a b c : A) : a + b + c = a + (b+c) := by
  rw [add_assoc]
