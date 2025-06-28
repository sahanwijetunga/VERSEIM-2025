--------------------------------------------------------------------------------
/-
Copyright (c) 2025 George McNinch. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Clea Bergsman, Katherine Buesing, George McNinch, Sahan Wijetunga
-/

/- VERSEIM-2025 REU -/

import Mathlib.Tactic

#check Prop 
#check Even 

example : Set ℤ := { n | Even n }

example : ({ 1 }:Set ℕ) = ({ 1 , 1 }:Set ℕ) := by
  ext
  simp

example (p q r : Prop) : p ∨ ( q ∧ r) → q ∨ p := by
  intro h
  rcases h with hp | ⟨hq,hr⟩

  

-- Set α *is* a function type: α → Prop 

-- think of Even as a predicate `α → Prop`


-- indexed union/intersection of sets

-- given types α and I, a function `I → Set α`
-- describes a family of `Set α`s indexed by the type `I`

-- for example, a sequence of sets `A₀, A₁, ...` (really: of `Set α`s)
-- is determined by a function `ℕ → set β`

example (α:Type) (A : ℕ → Set α) : Set α := by
  exact ⋃ i, A i


--------------------------------------------------------------------------------

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun x : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  apply εpos

theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  sorry

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  sorry

theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  sorry

theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  sorry

theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring


--------------------------------------------------------------------------------

example (p q : Prop) (hpq : p → q) (hnq : ¬q) : ¬p := by
  intro p
  have hq : q := hpq p
  absurd hnq hq


  -- fun hp : p =>
  -- show False from hnq (hpq hp)


--------------------------------------------------------------------------------

-- structures

-- let's consider complex numbers with rational real and imaginary part

 @[ext]
structure complex where
  re : ℚ
  im : ℚ


namespace complex

def myz0 : complex := ⟨ 1,2 ⟩
def myz1 : complex := complex.mk 1 2

#eval myz0
#eval myz1 

example ( a b : complex) (hr : a.re = b.re) (hi : a.im = b.im) : a= b := by
  ext
  repeat assumption 

example : myz0 = myz1 := by
  ext
  repeat rw [ myz0, myz1]

-- how to define functions on our new type??



def add ( a b : complex) : complex where
  re := a.re + b.re
  im := a.im + b.im

#eval add myz0 myz0 

def mul (a b : complex) : complex where
  re := a.re * b.re - a.im * b.im
  im := a.re * b.im + b.re * a.im

def conj (a:complex) : complex where
  re := a.re
  im := -a.im

#eval mul myz0 (conj myz0 )

def norm_sq (a:complex) : ℚ := 
  (mul a (conj a)).re

#eval norm_sq myz0 

end complex

structure mygroup where
  carrier : Type
  mul : carrier → carrier → carrier 
  e : carrier
  
  identity_law_l (g:carrier) : mul e g = g
  identity_law_r  (g:carrier) : mul g e = g

  assoc ( g h k : carrier) : mul (mul g h) k = mul g (mul h k)

  inverse (g : carrier) : ∃ h, mul g h = e

-- example : mygroup := 
--   mygroup.mk ....
