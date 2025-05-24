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
-- 02 -- Some tactics
----------------------------------------------------------------------------------

import Mathlib.Tactic


--------------------------------------------------------------------------------

/-

  Some conventions:

  - capitalized variable names like `P`, `Q`, `R` denote propositions
    (i.e. true/false statements)

  - variables whose names begin with `h` like `h1` or `hP` are proofs
    or hypotheses.


-/

-- I'm going to fix some variable names for propositions 
-- note that these are added into the `context` of anything I work on...

variable (P Q R : Prop)

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- part 1 

  -- Tactics we are going to introduce:

  -- - `exact`
  -- - `apply`
  -- - `intro` 


-- here is an example using `exact`

-- Assume that `P` and `Q` and `R` are all true. Deduce that `P` is true.

example (hP : P) (hQ : Q) (hR : R) : P := by

  -- note that `exact P` does *not* work. `P` is the proposition, `hP` is the proof.

  exact hP
  done



-- Assume `Q` is true. Prove that `P → Q`.
example (hQ : Q) : P → Q := by
  -- The goal is of the form `X → Y` so we can use `intro`
  intro h
  -- now `h` is the hypothesis that `P` is true.
  -- Our goal is now the same as a hypothesis so we can use `exact`
  exact hQ
  -- note `exact Q` doesn't work: `exact` takes the *term*, not the type.
  done


-- Assume `P → Q` and `P` is true. Deduce `Q`.
example (h : P → Q) (hP : P) : Q :=
  by
  -- `hP` says that `P` is true, and `h` says that `P` implies `Q`, so `apply h at hP` will change
  -- `hP` to a proof of `Q`.
  apply h at hP
  -- now `hP` is a proof of `Q` so that's exactly what we want.
  exact hP
  done 

-- we can prove the same statement with a different use of `apply`

-- Assume `P → Q` and `P` is true. Deduce `Q`.
example (h : P → Q) (hP : P) : Q :=
  by
  -- `h` says that `P` implies `Q`, so to prove `Q` (our goal) it suffices to prove `P`.
  apply h
  -- Our goal is now `⊢ P`.
  exact hP
  done

/-

  to summaryize:

  `apply h at hx` changes the hypotheses `hx` using the hypothesis `h`

  `apply h` changes the *goal*

-/

-- if you have a hypothesis `h : P → Q → R` and a goal `⊢ R`
-- then `apply h` replaces `⊢ R` with *two goals*, namely `⊢ P` and `⊢ Q`
example ( h : P → Q → R) : Q → P → R := by
  intro q p
  apply h
  · exact p  -- solve the first goal
  · exact q  -- solve the second goal
  done

/-
   The · are there to indicate the *cases*. They aren't *required*,
   but are used to (hopefully) make the proof more readable.

   You can type them with `\.` or `\cdot`
-/


--------------------------------------------------------------------------------

/- examples for you to try - group 1 -/

-- problem 1.1
example : P → Q → P := by
  sorry
  done

/- If we know `P`, and we also know `P → Q`, we can deduce `Q`.
   This is called "Modus Ponens" by logicians. -/

-- problem 1.2
example : P → (P → Q) → Q := by
  sorry
  done

/-- `→` is transitive. That is, if `P → Q` and `Q → R` are true, then
  so is `P → R`. -/

-- problem 1.3
example : (P → Q) → (Q → R) → P → R := by
  sorry
  done


-- problem 1.4
example : (P → Q → R) → (P → Q) → P → R := by
  sorry
  done

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- part 2 

-- tactics we introduce here
  -- `triv`
  -- `exfalso`



/- "trivial" proofs -/


-- Note that `True` is a `Prop`, i.e. a true-false statement that in this case is true.

-- `True` has a single proof, namely `True.intro`

example : True := True.intro

-- to give the trivial proof in tactics mode, use the `triv` tactic:

example : True := by
  trivial
  done


-- consider the following: 
example : (True → False) → False := by
  intro h
  -- we have a proof `h` of `True → False`
  apply h
  -- after applying h, we must prove `True`
  trivial
  done

-- another way to do the same proof:

example : (True → False) → False := by
  intro h
  exact (h True.intro)
  done

-- or working with proof-terms instead of tactics, we'd write:

example : (True → False) → False := 
  λ h => h True.intro

/- The exfalso tactic changes your goal to False. Why might you want
   to do that? Usually because at this point you can deduce a
   contradiction from your hypotheses (for example because you are in
   the middle of a proof by contradiction).
-/

example : P → (P → False) → Q := by
  intro x h
  exfalso       -- convert the goal to false, since we can obtain a contradiction from the hypotheses
  apply h x     -- use the contradiction to finish...
  done

-- using only proof-terms, this reads

example : P → (P → False) → Q := 
  λ x h => False.elim (h x)

--------------------------------------------------------------------------------

/- examples for you to try - group 2 -/

-- problem 2.1
example : True → True := by
  sorry
  done

-- problem 2.2
example : False → True := by
  sorry
  done

-- problem 2.3
example : False → False := by
  sorry
  done

-- problem 2.4
example : False → P := by
  sorry
  done

-- problem 2.5
example : True → False → True → False → True → False := by
  sorry
  done

-- problem 2.6
example : P → (P → False) → False := by
  sorry
  done

-- problem 2.7
example : (True → False) → P := by
  sorry
  done




--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

-- part 3 

-- we introduce the following tactics
--  `change`
--  `by_contra`
--  `by_cases`



-- negation

-- by *definition* the negation `¬ P`  of the proposition `P` is
-- `P → False`

-- i.e. `¬ P` and `P → False` are *equal by definition*.

-- for example, let's prove that `¬ True` implies `False`

example : ¬True → False := by
  intro h      -- now `h : ¬ True` which is the same as `h : True → False`
  apply h      -- after `apply`ing h, the goal is `⊢ True`
  trivial         -- and we can solve that goal with `triv`, the trivial proof
  done

-- the `by_contra` tactic allows us to prove a goal Q by assuming ¬ Q
-- and deriving a contradiction. In fact, it is equivalent to using
-- the equivalence `not_not : ¬ ¬ Q ↔ Q`.

-- note that since we have `not_not`, we have the law of the excluded middle
-- `∀ P, P ∨ ¬ P`.

-- let's see how to prove that `P` follows from `¬¬ P`:
example : ¬¬ P → P := by
  intro h            -- we have a term `h:¬¬ P` i.e. `h: ¬P → False`
  by_contra nh       -- we need to prove P, so we assume `¬P` and our goal becomes `⊢False`
                  -- now to solve the goal `False`, we can apply `h` to `nh`
                  -- (this is our "contradiction")
  exact h nh
  done

-- finally, the `by_cases g:P` tactic splits the goal into 2 cases. In the first case
-- `g:P` and in the second case `g:¬ P`.

-- let's use it to prove the following
example (P Q : Prop) : (P → Q) → (¬ P → Q) → Q := by
  intro h k
  by_cases xp : P
  · exact h xp
  · exact k xp
  done

--------------------------------------------------------------------------------

/- examples for you to try - group 3 -/

-- problem 3.1
example : False → ¬True := by
  sorry
  done

-- problem 3.2
example : ¬False → True := by
  sorry
  done

-- problem 3.3
example : True → ¬False := by
  sorry
  done

-- problem 3.4
example : False → ¬P := by
  sorry
  done

-- problem 3.5
example : P → ¬P → False := by
  sorry
  done

-- problem 3.6
example : P → ¬¬P := by
  sorry
  done

-- problem 3.7
example : (P → Q) → ¬Q → ¬P := by
  sorry
  done

-- problem 3.8
example : ¬¬False → False := by
  sorry
  done

-- problem 3.9
example : ¬¬P → P := by
  sorry
  done

-- the "contrapositive"
-- problem 3.10
example : (¬Q → ¬P) → P → Q := by
  sorry
  done
