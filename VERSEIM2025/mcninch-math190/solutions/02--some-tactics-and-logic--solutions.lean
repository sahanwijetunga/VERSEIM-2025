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
-- 02 -- Some tactics **solutions**
----------------------------------------------------------------------------------

import Mathlib.Tactic
--------------------------------------------------------------------------------

/- examples for you to try - group 1 -/

-- problem 1.1
example : P → Q → P := by
  intro p _
  exact p


/- If we know `P`, and we also know `P → Q`, we can deduce `Q`.
   This is called "Modus Ponens" by logicians. -/

-- problem 1.2
example : P → (P → Q) → Q := by
  intro p h
  apply (h p)
  done

/-- `→` is transitive. That is, if `P → Q` and `Q → R` are true, then
  so is `P → R`. -/

-- problem 1.3
example : (P → Q) → (Q → R) → P → R := by
  intro f g x
  apply g (f x)
  done

-- problem 1.4
example : (P → Q → R) → (P → Q) → P → R := by
  intro h g x
  apply h
  · exact x
  · exact g x
  done

--------------------------------------------------------------------------------

/- examples for you to try - group 2 -/


-- problem 2.1
example : True → True := by
  intro tt
  exact tt
  done

-- **or**

-- problem 2.1
example : True → True := by
  intro _
  trivial
  done

-- **or*
-- problem 2.1
example : True → True := λ x => x


-- problem 2.2
example : False → True := by
  intro f
  exfalso
  exact f
  done

-- **or**

-- problem 2.2
example : False → True := λ f => False.elim f


-- problem 2.3
example : False → False := by
  intro f
  exact f
  done

-- **or**

-- problem 2.3
example : False → False := λ x => x


-- problem 2.4
example : False → P := by
  intro f
  exfalso
  apply f
  done

-- problem 2.5
example : True → False → True → False → True → False := by
  intro _ f _ _ _ 
  apply f
  done

-- problem 2.6
example : P → (P → False) → False := by
  intro p h
  exfalso
  apply h p
  done

-- problem 2.7
example : (True → False) → P := by
  intro h
  exfalso
  apply h
  trivial
  done


-- --------------------------------------------------------------------------------
-- --------------------------------------------------------------------------------

-- /- examples for you to try - group 3 -/

-- problem 3.1
example : False → ¬True := by
  intro f
  exfalso
  exact f
  done

-- problem 3.2
example : ¬False → True := by
  intro _
  trivial
  done

-- problem 3.3
example : True → ¬False := by
  intro _
  intro f
  exact f
  done

-- **or**

-- problem 3.3
example : True → ¬False := by
  intro _ 
  exact (λ f => f) -- since `λ f => f : False → False` i.e. `λ f => f : ¬ False`
  done

-- (somehow it makes me unhappy that I can't replace `exact (λ f => f)` by
-- `apply (λ f => f)` in the preceding proof...)


-- problem 3.4
example : False → ¬P := by
  intro f
  exfalso
  apply f
  done

-- problem 3.5
example : P → ¬P → False := by
  intro p np
  apply np p
  done

-- problem 3.6
example : P → ¬¬P := by
  intro p     -- at this point, the goal is `¬¬P` which is a function type, namely
              -- `¬P → P`. So we can use the `intro` tactic 
  intro hnp   -- now `hnp : ¬P`
  apply hnp p
  done

-- ** or ** what is essentially the same

-- problem 3.6
example : P → ¬¬P := by
  intro p     
  exact λ hnp => hnp p
  done


-- ** or even **

-- problem 3.6
example : P → ¬¬P := λ p => (λ hnp => hnp p)


-- problem 3.7
example : (P → Q) → ¬Q → ¬P := by
  intro h nq
  intro p
  exact nq (h p)
  done

-- ** or just **

-- problem 3.7
example : (P → Q) → ¬Q → ¬P := λ h nq p => nq (h p)


-- problem 3.8
example : ¬¬False → False := by
  intro nnf
  apply nnf
  intro f
  exact f
  done

-- problem 3.9
example : ¬¬P → P := by
  intro nnp
  by_contra h
  exact nnp h
  done

-- the "contrapositive"
-- problem 3.10
example : (¬Q → ¬P) → P → Q := by
  intro h p   
  by_cases xq : Q
  · exact xq           -- in the first case, `xq : Q`
  · exfalso            -- in the second case, `xq : ¬Q`
                       -- we do an `exfalso` prove, so we need to construct a term of type `False`
                       -- 
                       -- now `h xq : ¬ P` i.e. `h xq : P → False`
                       -- so we find the term `(h xq) p : False`
    apply (h xq) p
  done

example : (¬Q → ¬P) → P → Q := by
  intro h p   
  by_cases xq : Q
  · exact xq           -- in the first case, `xq : Q`
  · have k := h xq     -- this produces a term of type `¬ P`
    contradiction      -- trivial contradiction is available, namely `k p`
  done
