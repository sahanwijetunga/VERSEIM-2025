--------------------------------------------------------------------------------
/-
Copyright (c) 2025 George McNinch. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Author : George McNinch
-/

/- VERSEIM-2025 REU -/

import Mathlib.Tactic

-- yesterday, we made a structure defining groups and proved in that structure
-- that `x*x = x → x = 1`

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
  have k : G.mul y (G.mul x x) = G.mul y x :=  by rw [h]
  rw [←G.mul_assoc y x x] at k
  unfold y at k
  rw [G.inv_mul_cancel x] at k
  rw [G.one_mul] at k
  assumption

-- the proof is perhaps not the prettiest, so here is a nicer proof
-- (using `mathlib`s notion of a group rather than our ad hoc notion.

-- the main reason I'm showing it is to show that sometimes it pays to
-- break tasks down into smaller pieces

lemma cancel {G : Type} [Group G] {g x y  : G} (h : g*x = g*y) : x = y := by
  rw [← one_mul x, ← one_mul y]
  rw [← inv_mul_cancel g]
  rw [mul_assoc, mul_assoc]
  rw [h]


example (G :Type) [Group G] (x:G) (h:x * x = x) :  x = 1 := by 
   nth_rw 3 [ ← mul_one x ] at h
   exact cancel h

--------------------------------------------------------------------------------

-- you should *read* the discussion on `hierarchies` in §8 of
-- mathematics-in-lean. Among other things, the text explains there how
-- operators like * and + are tied to lean-functions.

--------------------------------------------------------------------------------
