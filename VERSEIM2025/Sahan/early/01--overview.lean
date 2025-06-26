--------------------------------------------------------------------------------
/-
Copyright (c) 2024 George McNinch. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Author : George McNinch
-/

/-
course: Math 190 - Tufts University
instructor: George McNinch
semester: 2024 Spring
-/

--------------------------------------------------------------------------------
-- 01 -- Overview on Lean
--------------------------------------------------------------------------------

import Mathlib.Tactic

-- evaluation of expressions, and checking types

#check 8 + 9

#eval 8 + 9

#eval 8 - 11           -- this "difference" is interpreted as a *natural number*
#eval  (8 - 11 : ℤ)    -- but this is intepreted as an *integer*


def f ( x : ℕ ) := 20 * x + 3

#check f

-- evaluating a function is indicated just by justaposition.

#eval f 200

-- functions of several variables!

def g (x y : ℝ) := x^2 + y^2

#check g              -- `g` has type `ℝ → ℝ → ℝ`
#check g 1            -- `g 1` has type `ℝ → ℝ`
#check g 1 2          -- `g 1 2` has type `ℝ`
#eval g 1 2
                      -- note that Lean represents real numbers as limits of Cauchy sequences
                      -- of rational numbers; in this case, of the sequence `{ 5, 5, 5, ... }`

-- you can do some (relatively) ordinary programming languages stuff

def ll : List Int := [ 10, 20, -10 ]

#check ll
#eval ll

def ls : List String := [ "apples", "orange", "bananas" ]

#eval ls

-- join lists
#eval (ls ++ ls : List String)

-- can't join `ll` and `ls`, since they have different types (try it!!)
--#eval `ls ++ ll`

-- Propositions and such

def associativeLaw := (x y z : ℂ) → x * y * z = x * (y * z)

def associativeLaw' := ∀ x y z : ℂ, x*y*z = x*(y*z)

#check associativeLaw

-- there is already a proof of the associative law in MathLib which we
-- can use to prove our proposition

example : associativeLaw :=
  λ x y z => mul_assoc x y z

-- or

example : associativeLaw := by
  rintro x y z
  rw [mul_assoc]

def FermatLastTheorem :=
  ∀ x y z n : ℕ, n > 2 ∧ x * y * z ≠ 0 → x^n +  y^n ≠ z^n

#check FermatLastTheorem

-- don't know how to give a term of type FermatLastTheorem ...
theorem flt : FermatLastTheorem := sorry

-- [...snarky comment about the size of the margin of this page...??]

-- ## Example of proofs of a simple statement

-- here is "tactics proof" of a property regarding multiplication
-- of complex numbers

example (z w u : ℂ) : z * w * u = w * z * u := by
  rw [mul_comm z w]

-- you can recognize tactics proofs by the fact that they begin with
-- `by`.

-- a proof of the same statement via "proof terms" is slightly more
-- complicated, but I think we learn some useful things seeing it.

-- first of all, the function `congrArg` can be used to deduce that
-- if we know `a = b`, and if `f` is a function, then `f a = f b`

-- the signature of congrArg is **roughly**
--
-- `congrArg : (a₁ a₂ : α) → (f : α → β) → (h : a1 = a2) → f a₁ = f a₂`
--
-- here `α` and `β` are types (and the **actual** signature needs to mention them).

example (a b u : ℂ) ( h : a = b ) : a * u = b * u :=
   congrArg (λ g => g * u) h

-- so we can use `congrArg` to deduce that `z * w * u = w * z * u`
-- from the fact that we know `z*w = w*z` from the commutative law.

example (z w u : ℂ): z * w * u = w * z * u :=
  congrArg (λ g => g * u) (mul_comm z w)

-- **a subtlety**
-- the "arguments" can be given (as "parameters") as before, or they
-- can be given as part of the type. In that case, the "argumentation"
-- has to address "introducing" the variables

-- equivalent statement, but with arguments in the type
-- proof via tactics:
example :  (z w u : ℂ) → z * w * u = w * z * u :=  by
  rintro z w u
  rw [mul_comm z w]

-- the type `(z w u : ℂ) → z * w * u = w * z * u` is equivalent to
--          `∀ z w u : ℂ, ... `
-- i.e. for types `α` and `β` you can think of a function type
--   `α → β`
-- as being the same as the statement
--   `∀ a : α, β` or `∀ a : α, b : β`

-- **proof term version**. This time, I'm giving this term a name
-- rather than just giving it as an "example"
-- so I can use it just below...

def c : (z w u : ℂ) → z * w * u = w * z * u :=
  λ z w u => congrArg (λ g => g * u) (mul_comm z w)

#check c
#check c 2 3

-- notice that the *type* of the term `c` is `z * w * u = w * z * u`
-- and the *type* of the term `c 2 3` is `2 * 3 * u = 3 * 2 * u`

--------------------------------------------------------------------------------

-- Next, we are going to give a proof term (see below) of the result
-- that says (in English):`

--   (*)  if `m,n` are natural numbers, and if `n` is even, then `m * n` is also even.

-- Let's first understand how you prove *anything* is even.

-- Well, we introduce a type which characterizes *even-ness*. (I'm calling the type
-- `Even'` instead of just plain `Even` to avoid conflicts with existing
-- names in `mathlib`.)

def Even' ( n : ℕ ) : Prop :=
  ∃ r : ℕ, n = r + r

-- to demonstrate the proposition `Even' 4` we have to provide *evidence* that 4 is even.

-- the way to "give evidence" for an existence statement ("∃ r") is to
-- use the "introduction rule" `Exists.intro`

example : Even' 4 := Exists.intro 2 rfl

-- Or: we can use "anonymous consructor" `⟨...⟩` instead of the explict form:

example : Even' 6 := ⟨ 3, rfl ⟩

-- the *type* of term we must create to prove (*) is the following:

-- `(m : ℕ) → (n : ℕ) → ( hk : Even n ) → Even ( m * n )`

-- read this as follows: we are given terms `m` and `n` (of type `ℕ`) and a
-- term `hk` (of type `Even n`, which gives evidence that `n` is even), and we must produce a term
-- of type `Even ( m * n )` that gives evidence that `m * n` is even.

-- as your cursor moves through the arguments in the following proof, watch the `Lean infoview`
-- in `VSCode` -- you'll see the current state of the "goals" for the proof, until all are resolved.

example : ∀ m n : ℕ, Even' n → Even' (m * n) := by
  -- Say `m` and `n` are natural numbers, and assume `n=2*k`.
  rintro m n ⟨k, hk⟩
  -- We need to prove `m*n` is twice a natural number. Let's show it's twice `m*k`.
  use m * k
  -- Substitute for `n`,
  rw [hk]
  -- and now it's obvious.
  ring   -- here, `ring` is a tactic that can prove equalities in commutative (semi-)rings.
  -- or use rw [mul_add]

-- the above proof used the `use` tactic.
-- Note that before deploying the `use` tactic above, the `goal` was an existence statement:
-- (namely we needed to construct a term of type `Even' n*m`).
-- After `use`, the `goal` is `m * n = m * k + m * k`. In other words, we are left to prove
-- that `m*k`, the term we `use`d, really "works" to verify the existence proof.

-- ####

-- alternatively, we can avoid `use` and instead construct available hypotheses
-- using the `have` tactic:
-- In the proof below, try positioning the cursor on the line *following* the
-- conclusion of the `have` tactic.

-- At this point, the `Lean infoview` shows that the goal is still to construct
-- a term of type `Even' n*m`. But now we have an additional hypothesis `hmk`
-- which we can use to close the goal.

example : ∀ m n : ℕ, Even' n -> Even' (m*n) := by
  rintro m n ⟨k, hk⟩
  -- this time, we utilize `have` instead of `use`
  have hmk : m * n = m * k + m * k := by
     rw [hk]
     ring
  -- and now we are done
  exact ⟨ _ , hmk ⟩  -- or `exact ⟨ m*k , hmk ⟩`
  -- or somewhat more verbosely:  exact `Exists.intro _ hmk` or `Exists.intro m*k hmk`.
