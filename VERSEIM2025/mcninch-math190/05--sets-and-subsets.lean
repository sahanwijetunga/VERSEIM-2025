/-
Copyright (c) 2024 George McNinch. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Author : George McNinch
-/

/-
course: Math 190 - Tufts University
instructor: George McNinch
semester: 2024 Spring
-/

import Mathlib.Tactic

--------------------------------------------------------------------------------
-- 05 -- Sets and subsets
--------------------------------------------------------------------------------

/- to quote from `Math in Lean`

> Lean’s library does define elementary set-theoretic notions. In
> contrast to set theory, in Lean a set is always a set of objects of
> some type, such as a set of natural numbers or a set of functions
> from real numbers to real numbers. The distinction between types and
> sets takes some getting used to

-/

variable (α:Type)  -- out ambient type

-- examples of types include things like `ℕ`, the natural numbers,
-- `ℝ`, the real numbers, ...

-- `Set α` is a Type whose terms are "subset of α", or more precisely,
-- "sets consisting of elements of type α"

variable (s t u : Set α)
variable (x y z : α)

-- usual set-theoretic operations are defined

#check x ∈ s    -- the proposition that `x` is an element of `s`

#check s ⊂ t    -- the proposition that `s` is a proper subset of `t`

example : (¬ x ∈ s) = (x ∉ s) := rfl

-- type `ε` as  `\in`, `∉` as `\notin` 

example : x ∈ s ∪ t ↔ x ∈ s ∨ x ∈ t := by simp


example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intro x ⟨xs,xu⟩
  exact ⟨ h xs, xu ⟩

-- to prove that two sets are equal, it suffices to show that every
-- element of one is an element of the other. This principle is known
-- as “extensionality” and there is a tactic called `ext` that handles it

example : s ∪ t = t ∪ s := by
  ext x             -- x is the name for the element used to test extensionality
                    -- if you look in the lean context, you'll see that it *shadows* the "global"
                    -- variable x we created with the `variable` statement
  -- now the goal is `⊢ x ∈ s ∪ t ↔ x ∈ t ∪ s`
  constructor
  · intro h
    simp
    rcases h with hs | ht
    · right
      exact hs
    · left
      exact ht
  · intro h
    simp
    rcases h with ht | hs
    · right
      exact ht
    · left
      exact hs
  done


-- we can use `set-builder notation` to define sets

-- let's consider a predicate on our type α

variable (P : α → Prop)

-- using `P` we can define a term of type `Set α`

example : Set α := { x | P x }

-- a concrete example of a predicate is `Even : ℕ → Prop` found in the lean library 

#check Even

def evens : Set ℕ := { n | Even n }

def odds : Set ℕ := { n | ¬ Even n }

-- more generally, we can  define

def hasP {α:Type} (P:α → Prop) : Set α := { y | P y }
def notP {α:Type} (P:α → Prop) : Set α := { y | ¬ P y }

#check hasP P

-- there are two terms of type `Set α` that are always present
-- `∅ : Set α` and `univ : Set α`

-- lets prove that `hasP ∪ notP = univ` and `hasP ∩ notP = ∅`

open Set  -- this gives us access to `Set.univ` etc, without typing `Set`

-- lets prove for any proposition that `(hasP P) ∪ (notP P) = univ`

theorem checkUnion (α:Type) (P:α → Prop)  : (hasP P) ∪ (notP P) = (univ:Set α) := by 
   rw [ hasP, notP ]
   ext y
   simp
   apply Classical.em      -- excluded middle!
   done

-- and lets use our theorem to prove that `evens ∪ odds = ℕ`

example : evens ∪ odds = univ := by
  rw [ evens, odds ]
  have h := checkUnion ℕ Even  
  rw [ hasP, notP] at h
  exact h

-- now lets prove that `(hasP P) ∩ (notP P) = ∅`

theorem checkInt (α:Type) (P:α → Prop) : (hasP P) ∩ (notP P) = ∅ := by
  rw [ hasP, notP ]
  ext y
  simp

-- and lets use this to prove that `evens ∩ odds = ∅`.

example : evens ∩ odds = ∅ := by
  rw [evens,odds]
  have h := checkInt ℕ Even
  rw [hasP,notP] at h
  exact h

-- finally , let's define the predicate `isNonNegative` on `ℝ`
-- and use the above result to show that 
-- `ℝ = { y | y ≥ 0 } ∪ { y | y < 0 }`

def isNonNegative (a:ℝ) : Prop := a≥0

example : { y:ℝ | y ≥ 0 } ∪ { y:ℝ | y < 0 } = (univ:Set ℝ) := by
  have h := checkUnion ℝ isNonNegative
  rw [hasP,notP] at h
  ext y
  rw [←h]
  unfold isNonNegative
  simp
  

--------------------------------------------------------------------------------

-- notation for operations on subsets via functions
--
-- if `f:α → β` and `s:Set α`, `t:Set β`, 
-- the image of s is denoted `f '' s`
-- the inverse image of t is denoted `f⁻¹' t`

variable (β : Type)
variable (s : Set α)
variable (t : Set β)
variable (f : α → β)


#check f '' s   -- has type `Set β`

#check f⁻¹' t   -- has type `Set α`


-- let's prove that `s` is contained in the inverse image of the image
-- of `s`.  we use the `show` tactic, which we haven't mentioned
-- before.

example : s ⊆ f ⁻¹' (f '' s) := by
 intro x hxs
 show f x ∈ f '' s
 use x

-- The show tactic can actually be used to rewrite a goal to something
-- definitionally equivalent:

example (n : ℕ) : n + 1 = Nat.succ n := by
  show n + 1 = n + 1
  rfl


-- note the definitional equivalence:

example : (x ∈ f ⁻¹' (f '' s)) = (f x ∈ f '' s) := rfl

--  this can be done directly with `image_subset_iff`

example : s ⊆ f ⁻¹' (f '' s) := by
 apply image_subset_iff.mp 
 rfl
 

-------- other direction

example : f '' (f ⁻¹' T) ⊆ T := by 
  rintro z ⟨y, hy, eq⟩
  rw [←eq]
  exact hy


-- `rfl` trick
-- requires use of `rintro` rather than `intro`

example : f '' (f ⁻¹' T) ⊆ T := by 
  rintro _ ⟨y, hy, rfl⟩
  exact hy



