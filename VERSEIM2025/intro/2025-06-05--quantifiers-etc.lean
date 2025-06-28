--------------------------------------------------------------------------------
/-
Copyright (c) 2025 George McNinch. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Clea Bergsman, Katherine Buesing, George McNinch, Sahan Wijetunga
-/

/- VERSEIM-2025 REU -/

import Mathlib.Tactic

-- follow-up on yesterday's discussion about functions and "currying"
-- (though I'm not sure I used the word currying...)

def F : ℤ → ℤ → ℤ := fun x y => x + y

def F' : ℤ × ℤ → ℤ := fun (x,y) => x + y

#eval F' (1,0)

-- this next evaluation is only happy because Lean coerces `1:ℤ` into `(1,1):ℤ × ℤ`
-- which you can tell because `F' 1` evaluates to 1+1 = 2.

#check F' (1:ℤ)
#eval F' 1

-- but Lean for whatever reason does not coerce= a `String` into a `String × String`

def Fs : String × String → String := fun (x,y) => String.append x y

#eval Fs ("foo","bar")

-- but this fails:
--#eval Fs "foo"

--------------------------------------------------------------------------------

-- yesterday we saw a bit about the ∀ quanitifier. 

-- let's look at some other "logical operators" now

-- an operator (∀, ∃, ∧ , ∨ , ⋯ ) produces a type. there are then two questions:

-- how does one *use* a term of the indicated type?
-- how does one *create* a term of the indicated type?

-- we saw that ∀ was basically the same as (some form of) a function type

-- now lets look at the existential quantifier ∃

-- a basic example is divisibility of natural numbers

-- let's prove that 2m ∣ 4m. 

example (m : ℕ) : ∃ x:ℕ, x * 2 * m = 4*m := by
  use 2

-- so to give the proof, we have to *provide* the required x via `use`

example : ∃ x : ℝ, 0 < x ∧ x < 1 := by
  use 1 / 2
  norm_num

-- rather than rely on the norm_num tactic, we can settle all the
-- goals of the required ∧ assertion:

example : ∃ x : ℝ, 0 < x ∧ x < 1 := by
  have h : (0:ℝ) < 1/2 := by norm_num
  have k : 1/2 < (1:ℝ) := by norm_num
  use 1/2  -- the use tactic uses available assumptions.
  

-- now let's see how to *use* a term of a type involving ∃ as a  hypothesis:

def has_zero (f : ℝ → ℝ) : Prop := ∃ (x:ℝ), f x = 0

example (f g: ℝ → ℝ) (h: has_zero f) : 
  has_zero fun x => f x * g x := by
  rcases h with ⟨y,hf⟩
  use y
  dsimp
  rw [hf]
  norm_num

-- here if h has type `∃ x:α, p`
-- then `rcases h with ⟨y,hy⟩` gives you a term `y:α` and a term `h:p`
-- here you should think of `h` as a proof that `p holds for y`.

-- the syntax ⟨ ... ⟩ is Lean's "anonymous constructor syntax"
-- if you look at `math-in-lean` section 3.2 you'll see some more examples of
-- how to use terms like this. 


-- another version of the "bounded" predicates  from yesterday

--recall

def FnUb (f:ℝ → ℝ) (a:ℝ) : Prop :=
  ∀ x, f x ≤ a

-- here is a version that doesn't require indicating the `a`

def FnHasUb (f:ℝ → ℝ) : Prop :=
  ∃ a, FnUb f a


def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a

-- we proved this yesterday, but are now *naming* it.
-- note the "implicit arguments" `f g` and `a b`

-- and here we give a `term proof` instead of a `tactic proof`

theorem FnUb_add {f g : ℝ → ℝ} {a b : ℝ} (hfa : FnUb f a) (hgb : FnUb g b) :
    FnUb (fun x ↦ f x + g x) (a + b) := 
    fun x ↦ add_le_add (hfa x) (hgb x)


example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x => f x + g x := by
  rcases ubf with ⟨ a, ubfa ⟩
  rcases ubg with ⟨ b, ubgb ⟩
  use a + b
  exact FnUb_add ubfa ubgb


-----

-- exercise

def divis (n m : ℕ) : Prop := ∃ x:ℕ, x*n = m 

example { n : ℕ} : divis n n := by sorry


example {n m p :ℕ} (h: divis n m) (k: divis m p) : divis n p := by
  sorry

-- exercise: give the proofs about even and odd functions:

def FnEven (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = f (-x)

def FnOdd (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = -f (-x)

example (ef : FnEven f) (eg : FnEven g) : FnEven fun x ↦ f x + g x := by
  intro x
  calc
    (fun x ↦ f x + g x) x = f x + g x := rfl
    _ = f (-x) + g (-x) := by rw [ef, eg]


example (of : FnOdd f) (og : FnOdd g) : FnEven fun x ↦ f x * g x := by
  sorry
  
example (ef : FnEven f) (og : FnOdd g) : FnOdd fun x ↦ f x * g x := by
  sorry

example (ef : FnEven f) (og : FnOdd g) : FnEven fun x ↦ f (g x) := by
  sorry

--------------------------------------------------------------------------------

--negation

-- symbol ¬ typed via \not

-- in Lean, there is a type `False` that has no terms (so you can't prove it).
-- The negation `¬ P` of a proposition P is a term of type `P → False`,
-- think of this as saying that `P` implies a contradiction.

variable (a b :ℝ)

-- let's prove that " a< b -> not b < a "

-- we will use that " a < a is false " 

-- and we'll use the transitivity of the relation <, which is named `lt_trans`

--example (h : a < b) : ¬b < a := by
example (h : a < b) : b < a → False := by
  intro h'
  have : a < a := lt_trans h h'
  apply lt_irrefl a this

#check lt_irrefl

-- note that as soon as we intro h', our goal is `False`

-- lt_irrefl.{u_1} {α : Type u_1} [Preorder α] (a : α) : ¬a < a

-- note that lt_irrefl a this returns a term of type ¬ a < a -- in other words
-- a proof that `a < a → False`.


example (h : ∀ a, ∃ x, f x > a) : ¬FnHasUb f := by
  intro fnub
  rcases fnub with ⟨a', fnuba⟩
  rcases h a' with ⟨x, hx⟩
  have : f x ≤ a' := fnuba x
  linarith


-- try this one:

example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f := by
  sorry 

example : ¬FnHasUb fun x ↦ x :=
  sorry


variable {α : Type*} (P : α → Prop) (Q : Prop)

example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  intro x
  intro hpx 
  apply h
  use x


example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  intro kxp    
  rcases kxp with ⟨x,hx⟩ 
  exact h x hx

example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  sorry


--------------------------------------------------------------------------------

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  show P x
  by_contra h''
  exact h' ⟨x, h''⟩
