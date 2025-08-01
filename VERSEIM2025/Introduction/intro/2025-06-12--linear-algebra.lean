 --------------------------------------------------------------------------------
/-
Copyright (c) 2025 George McNinch. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Clea Bergsman, Katherine Buesing, George McNinch, Sahan Wijetunga
-/

/- VERSEIM-2025 REU -/

import Mathlib.Tactic

-- well, first some group theory

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
  rw [mul_assoc _ g x , mul_assoc _ g y]
  rw [h]

example (G :Type) [Group G] (x:G) (h:x * x = x) :  x = 1 := by 
   nth_rw 3 [ ← mul_one x ] at h
   exact cancel h

--------------------------------------------------------------------------------

-- you should *read* the discussion on `hierarchies` in §8 of
-- mathematics-in-lean. Among other things, the text explains there how
-- operators like * and + are tied to lean-functions.

--------------------------------------------------------------------------------
-- ring has two operations: + and * 

-- a field is a commutative ring in which every non-zero element has an inverse

-- in lean, the inversion function has a funny property(!)

#eval ((2/3)⁻¹:ℚ)
#eval (0⁻¹:ℚ)

example : Field ℚ := inferInstance

noncomputable
example : Field ℂ := inferInstance

-- OTOH this fails because ℤ doesn't have a field instance

--example : Field ℤ := inferInstance  
example : CommRing ℤ := inferInstance 

-- for any commutative ring we can consider a module over it

-- in such a structure we can form linear combinations of elements

example (R:Type) [CommRing R] (M:Type) [AddCommGroup M] [Module R M] (r s:R) (m n:M) : M 
  := r • m + s • n

-- scalar multiplication is denoted \smul • 

-- for the time being, we are going to be interested in *vector spaces*, which just amount
-- to *modules over field* -- i.e the special case in which R is a field

--

variable (k:Type*) [Field k]
variable (V:Type*) [AddCommGroup V] [Module k V]

-- some "built-in" properties reflecting axioms you probably saw in
-- linear algebra class

example (a : k) (u v : V) : a • (u + v) = a • u + a • v := by
  module 
  --smul_add a u v

example (a b : k) (u : V) : (a + b) • u = a • u + b • u :=
  add_smul a b u

example (a b : k) (u : V) : a • b • u = b • a • u :=
  smul_comm a b u

example (u:V) : 1 • u = u := by
  module 


-- a standard example of vector space is " k ^ n " which Lean writes as `Fin n → k`

example (n :ℕ) : AddCommGroup (Fin n → k) := inferInstance

example (n :ℕ) : Module k (Fin n → k) := inferInstance



-- for example, we can add and scalar-multiply terms of type `Fin n → k`

example (n : ℕ) (v w : Fin n → k) (t : k ) : Fin n → k := t • v + w

-- similarly, k can be treated as a (1-dimensional) vector space over
-- itself

example : Module k k := inferInstance

-- in `Module k k` scalar multiplication is just multiplication 


example (t s:k) : t•s = t*s := rfl

-- Linear maps

variable (W:Type*) [AddCommGroup W] [Module k W]

-- the type of linear maps from V to W is an "arrow type", with extra syntax, namely

-- \to_l[k]  gives →ₗ[k]

#check V →ₗ[k] W

variable (φ ψ : V →ₗ[k] W)

-- note that `V →ₗ[k] W` is itself a vector space

example : Module k (V →ₗ[k] W) := inferInstance

-- thus we can form linear combinations of our φ and ψ:

#check 2•φ + ψ

-- how to generate a "skeleton" for a structure ...
example : V →ₗ[k] V := _
