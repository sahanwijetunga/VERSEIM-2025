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
-- is determined by a function `ℕ → set α`

example (α:Type) (A : ℕ → Set α) : Set α := by
  exact ⋃ i, A i


example (n: ℕ ) (s: Fin n → ℝ) : ℝ := ∑ i, s i


#check Even
#check Prop

-- def a : Set ℤ := {n | Even n}

-- def b : Set ℤ := {n ∈ a| ¬ Even n}

example: ({1}: Set ℕ ) = ({1,1}: Set ℕ ) := by
  ext x
  constructor
  . simp
  . simp



-- structs


namespace sahan

@[ext]
structure complex where
  re: ℚ
  im: ℚ

def a: complex := ⟨2, 3⟩

def b : complex := complex.mk 1 2

def c: complex where
  re:=2
  im:=3

example: a=c := by
  ext
  . rw[a, c]
  . rw[a,c]
def add (a b: complex) : complex where
  re := a.re+b.re
  im :=a.im+b.im

def mul (a b: complex) : complex where
  re := a.re*b.re-a.im*b.im
  im :=  a.re*b.im+a.im*b.re

-- example (h: 4=2+2) : 4=6 := by
--   repeat rw[h, <- h]

theorem add_assoc (a b c: complex): add (add a b) c = add a (add b c) := by
  ext
  . repeat rw[add]
    simp
    rw[Rat.add_assoc]
  . repeat rw[add]
    simp
    rw[Rat.add_assoc]

def conj (a: complex): complex where
  re := a.re
  im := -a.im

#eval mul a (conj a)

def norm_sq (a: complex) : ℚ :=
  (mul a (conj a)).re

#eval norm_sq a

end sahan


structure mygroup where
  carrier: Type*
  mul: carrier -> carrier -> carrier
  e: carrier

  identity_law_l (g: carrier) : mul e g = g
  identity_law_r (g: carrier) : mul g e = g

  assoc (a b c: carrier): mul (mul a b) c = mul a (mul b c)

  inverse (a: carrier): ∃b, mul a b = e

example : mygroup where
  carrier := ℤ
  mul := (.+.)
  e := 0
  identity_law_l := by
    intro n
    rw[Int.zero_add]
  identity_law_r := by
    intro n
    rw[Int.add_zero]
  assoc := fun _ _ _ => add_assoc _ _ _
  inverse := by
    intro n
    use -n
    ring

def foo :=
  let a := Nat
  fun x : a => x + 2
/-
  def bar := (fun a => fun x : a => x + 2) Nat
-/

structure two_simplex where
  x: ℚ
  y: ℚ
  z: ℚ
  x_nonneg : 0 ≤ x
  y_nonneg : 0 ≤ y
  z_nonneg : 0 ≤ z
  sum_eq: x+y+z=1

def a: two_simplex where
  x := 0.1
  y := 0.2
  z := 0.7
  x_nonneg := by norm_num
  y_nonneg:= by norm_num
  z_nonneg:= by norm_num
  sum_eq := by norm_num

#eval a

def swapXy (a : two_simplex) : two_simplex
    where
  x := a.y
  y := a.x
  z := a.z
  x_nonneg := a.y_nonneg
  y_nonneg := a.x_nonneg
  z_nonneg := a.z_nonneg
  sum_eq := by linarith[a.sum_eq]

#eval swapXy a

structure StandardSimplex (n: ℕ) where
  V: Fin n -> ℝ
  NonNeg : ∀ i, 0 ≤ V i
  sum_eq_one: (∑ i: Fin n, V i) =1


namespace StandardSimplex

noncomputable
def midpoint (n : ℕ) (a b : StandardSimplex n) : StandardSimplex n
    where
  V i := (a.V i + b.V i) / 2
  NonNeg := by
    intro i
    apply div_nonneg
    · linarith [a.NonNeg i, b.NonNeg i]
    norm_num
  sum_eq_one := by
    simp [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_add_distrib,
      a.sum_eq_one, b.sum_eq_one]
    field_simp

end StandardSimplex


structure Group₁ (α: Type*) where
  mul: α -> α -> α
  one: α
  inv: α → α
  mul_assoc: ∀ x y z: α, mul (mul x y) z = mul x (mul y z)
  mul_one: ∀ x: α, mul x one = x
  one_mul: ∀ x: α, mul one x = x
  inv_mul: ∀ x: α, mul (inv x) x = one

-- #check Group

variable (α β γ : Type)

#check Equiv α β
#check α ≃ β

-- variable (f: α ≃ β)

-- #check (f: α → β) -- f.toFun
-- -- #check (f⁻¹: β → α)
-- #check (f.invFun: β → α)

-- #check (Equiv.trans (Equiv.refl α) f: α → β)
-- #check (f ∘ Equiv.refl α : α → β)

#check Function.RightInverse

example: Group₁ (α ≃ α) where
  mul := Equiv.trans
  one := Equiv.refl α
  inv := Equiv.symm
  mul_assoc := Equiv.trans_assoc
  mul_one := Equiv.refl_trans
  one_mul := Equiv.trans_refl
  inv_mul := Equiv.symm_trans_self
