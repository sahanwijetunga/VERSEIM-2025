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

----------------------------------------------------------------------------------
-- 03 -- more logic
----------------------------------------------------------------------------------

import Mathlib.Tactic


-- As far as basic logical operations are concerned, we still need to introduce
-- "and", "or", and "iff".

-- we again work with some fixed variable names for propositions

variable (P Q R S : Prop)

-- Now `P ∧ Q` denotes the proposition "`P` and `Q`"
-- We could also write it as `And P Q`.

-- how to get a term of type `P ∧ Q`

-- use the `constructor` tactic:

example : P → Q → P ∧ Q := by
  intro p q 
  constructor
  · exact p
  · exact q
  done

-- arguably easier to just use the "introduction rule for And", though:

example : P → Q → P ∧ Q := by
  intro p q
  exact And.intro p q
  -- or just `exact ⟨p, q⟩`

example (p:P) (q:Q) : P ∧ Q := 
  ⟨ p , q ⟩  
  -- or 
  -- And.intro p q


-- note that we can take apart a term of type `P ∧ Q` while using the `intro` tactic:
example : P ∧ Q → Q := by
  intro ⟨_,h₂⟩  -- now `h₀:P` and `h₁:Q`
  exact h₂
  done

-- sometimes we need to "take apart" a term of type `P ∧ Q` present in the context
-- we can use the `cases` tactic

example : P ∧ Q → Q := by
  intro hpq
  cases hpq with
  | intro _ q => exact q
  


--------------------------------------------------------------------------------
-- problems for you to work on - group 1
--


-- problem 1.1
example : (P → Q → R) → P ∧ Q → R := by
  sorry
  done

-- problem 1.2
example : P → Q → P ∧ Q := by
  sorry
  done

-- problem 1.3
/-- `∧` is symmetric -/
example : P ∧ Q → Q ∧ P := by
  sorry
  done

-- problem 1.4
example : P → P ∧ True := by
  sorry
  done

-- problem 1.5
example : False → P ∧ False := by
  sorry
  done

-- problem 1.6
/-- `∧` is transitive -/
example : P ∧ Q → Q ∧ R → P ∧ R := by
  sorry
  done

-- problem 1.7
example : (P ∧ Q → R) → P → Q → R := by
  sorry
  done

--------------------------------------------------------------------------------

-- logical equivalence

-- `P ↔ Q` is a Proposition which asserts that "P iff Q".

-- you can think of it as follows:
-- `P ↔ Q` is the same as `(P → Q) ∧ (Q → P)`.

-- given a term `h : P ↔ Q`, you can write

-- `h.1 : P → Q` and `h.2 : Q → P`

-- or equivalently

-- `h.mp : P → Q` and `h.mpr : Q → P`.

-- you can also use the `cases` tactic to extract the two parts

example : (P ↔ Q) → (Q → P) := by
  intro heq
  cases heq with
  | intro mp mpr => exact mpr
  done

-- **or**

example : (P ↔ Q) → (Q → P) := by
  intro heq
  exact heq.mpr

-- **or**

example : (P ↔ Q) → (Q → P) := by
  intro ⟨_,hmpr⟩
  exact hmpr

-- let's prove the following:

example : P ↔ P := by 
  have h : P → P := by
    intro xp; exact xp
  -- or `have h: P → P := λ p => p`
  exact ⟨ h, h ⟩
  done


-- *or just*

example : P ↔ P := by rfl

-- you can start and stop a namespace

namespace my_iff

def iff_symm { P Q : Prop } (h: P ↔ Q) : (Q ↔ P) := by
  exact ⟨ h.mpr, h.mp ⟩
  done

-- I can *use* the term `iff_symm h` inside the namespace.
-- after the end of the namespace, one must write `my_iff.iff_symm h`

-- we can use this term to prove a more involved result

example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor
  · intro hf; exact iff_symm hf
  · intro hr; exact iff_symm hr
  done

end my_iff

-- here is a different (better!) - `tactic`s proof

example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor <;>
    · intro h
      rw [h]
  done


-- to grok the `constructor <;>` construction, see here:
-- https://lean-lang.org/theorem_proving_in_lean4/tactics.html?highlight=constructor#more-tactics
--
-- the point is that: "In t₁ <;> t₂, the <;> operator provides a
-- parallel version of the sequencing operation: t₁ is applied to the
-- current goal, and then t₂ is applied to all the resulting subgoals..."

-- after the `constructor <;>` tactic is run, one of the 
-- goals is: `⊢(Q ↔ P) → (P ↔ Q)`. 
-- after `intro h`, we have `h : Q ↔ P`, and after `rewrite [h]`
-- the goal becomes `P ↔ P` which is true by the reflexive law.

--------------------------------------------------------------------------------
-- problems for you to work on -- group 2

-- problem 2.1
example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  sorry
  done

-- problem 2.2
example : P ∧ Q ↔ Q ∧ P := by
  sorry
  done

-- problem 2.3
example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  sorry
  done

-- problem 2.4
example : P ↔ P ∧ True := by
  sorry
  done

-- problem 2.5
example : False ↔ P ∧ False := by
  sorry
  done

-- problem 2.6
example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  sorry
  done

-- problem 2.7
example : ¬(P ↔ ¬P) := by       
  sorry
  done

--------------------------------------------------------------------------------
-- manipulation of `P ∨ Q`

-- The canonical way to prove a disjunction `P ∨ Q` is to prove `P` or to
-- prove `Q`. The `left` tactic chooses `A`, and the `right` tactic chooses `B`

-- For example

example : Q → P ∨ Q := by
  intro hq
  right 
  exact hq
  done

-- the definition of the disjunction looks something like the following:

inductive Or' (α : Prop) (β : Prop) where
  | inl' : α → Or' α β
  | inr' : β → Or' α β

-- so e.g. we can make a new type

example : P → Or' P Q := λ hp => Or'.inl' hp

-- to use the Lean's "real" disjuction we can use
-- i.e. `inl` and `inr` are the `constructors` for the `Or` type

example : Q →  P ∨ Q := λ hq => Or.inr hq


-- let's consider a more complicated example
-- if we have a hypotheses `hpq : P ∨ Q`
-- we can handle the two possibities: `hpq == inl hp` or `hpq == inr hq`
-- using a 'cases' statement
example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro hpq f g
  rcases hpq with hp | hq    -- this produces two subgoals, labelled by the possibilities
  { -- hp in context here
    apply f
    exact hp
  }
  { -- hq in context here
    apply g
    exact hq
  }
  done

-- symmetry of ∨

-- symmetry of `or`
example : P ∨ Q → Q ∨ P := by
  intro hqp
  rcases hqp with hp | hq
  { right
    exact hp
  }
  { left
    exact hq
  }
  done

example : P ∨ Q → Q ∨ P := by
  intro hqp
  rcases hqp with hp | hq
  { right
    exact hp
  }
  { left
    exact hq
  }
  done

 
-- let's prove half of the deMorgan laws 

example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor 
  case mp =>
    intro h
    constructor 
    case left =>
      intro hp
      apply h
      left
      exact hp
      done
    case right =>
      intro hq
      apply h
      right
      exact hq
      done
    done
  case mpr =>
    intro ⟨ hnp, hnq ⟩
    intro pOq
    cases pOq
    case inl h =>
      apply hnp
      exact h
    case inr h =>
      apply hnq
      exact h
    done
  done


example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor 
  {
    intro h
    constructor 
    {
      intro hp
      apply h
      left
      exact hp
      done
    }
    {
      intro hq
      apply h
      right
      exact hq
      done
    }     
    done
  }
  {
    intro ⟨ hnp, hnq ⟩
    intro pOq
    rcases pOq with hp | hq
    {
      apply hnp
      exact hp
    }
    {
      apply hnq
      exact hq
    }
  }
  done

--------------------------------------------------------------------------------
-- group 3
-- try the other half of deMorgan, as an exercise

example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  sorry
  done
