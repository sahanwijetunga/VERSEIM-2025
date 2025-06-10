--------------------------------------------------------------------------------
/-
Copyright (c) 2025 George McNinch. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Author : George McNinch
-/

/- VERSEIM-2025 REU -/

import Mathlib.Tactic

def F : ℕ → (ℕ → ℕ) :=
  fun x y =>  x^y + y

#eval F 2 500


#check F 0

def F' : ℤ × ℤ → ℤ :=
  fun (x,y) => x + y



def foo (s t :String) : ℤ :=
   match s,t with
   | "george",_ => 1
   | "sahan" ,_=> 2
   | "clea",_ => 3
   | _,"zoo" => 5
   | _,_ => 6

#eval foo "asdfasdf" "zoo"





-- let's talk about quantifiers

-- (I'm borrowing these examples from math-in-lean...)

-- Let's parse this statement

#check ∀ x : ℝ, 0 ≤ x → |x| = x

-- this thing is a proposition, so far, it might or might not be true!

-- as far as Lean is concerned, the above statement is really just the
-- same type as

#check (x:ℝ) → 0 ≤ x → |x| = x

-- or event

#check (x:ℝ) → 0 ≤ x → abs x = x

#check abs_of_nonneg

example : ∀ x : ℝ, 0 ≤ x → |x| = x := by
  intro x h
  exact abs_of_nonneg h

example (x: ℝ): x + 0 = x := by
  rw[add_zero]

example (x: ℝ): x + 0 = x := by
  exact add_zero x


-- let's define some *predicates* on real-valued functions of a real variable

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnBoundedByFn (f g : ℝ → ℝ) : Prop :=
  ∀ x, f x ≤ g x


-- read: `FnUB f a` means that the values of function `f` are bounded
-- above by `a`

section anon_functions

-- the keyword `fun` constructs a function. The `fun` construction is
-- often called a `lambda` in some programming languages ("anonomous
-- function")

-- for example

def f : ℝ → ℝ → ℝ := fun x y => x + y

-- same as

def f' : ℝ → ℝ → ℝ := by
  intro x y
  exact x + y

-- you can apply anonymous functions just by juxtaposition

#eval (fun x y => x + y) 1 2

end anon_functions

-- in the following example, note how `apply`ing `add_le_add` results in two new goals.

variable  (f g : ℝ → ℝ )

example (hfa : FnUb f a) (hgb : FnUb g b) :
  FnUb (fun x ↦ f x + g x) (a + b) := by
  intro x
  dsimp
  apply add_le_add
  · --proving first goal
    apply hfa
  · --proving second goal
    apply hgb

#check add_le_add

-- try these!

example (hfa : FnLb f a) (hgb : FnLb g b) : FnLb (fun x ↦ f x + g x) (a + b) :=
  sorry

example (nnf : FnLb f 0) (nng : FnLb g 0) : FnLb (fun x ↦ f x * g x) 0 :=
  sorry

example (hfa : FnUb f a) (hgb : FnUb g b) (nng : FnLb g 0) (nna : 0 ≤ a) :
    FnUb (fun x ↦ f x * g x) (a * b) :=
  sorry


--------------------------------------------------------------------------------

example ( P Q : Prop) : P ∧ Q → Q := by
  intro ⟨hp,hq⟩
  exact hq

example ( P Q : Prop) : P  → P ∨ Q := by
