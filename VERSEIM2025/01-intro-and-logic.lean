--------------------------------------------------------------------------------
/-
Copyright (c) 2025 George McNinch. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Author : George McNinch
-/

/- VERSEIM-2025 REU -/

import Mathlib.Tactic

-- Let's start out by proving confirming identities about natural numbers

-- we expect the statement "x * y = y * x" to be true for natural numbers.
-- and it is. It is even a result we can find in `mathlib`.

-- If we look at 

#check mul_comm

#check mul_assoc

-- we see the signatures

-- mul_comm.{u_1} {G : Type u_1} [CommMagma G] (a b : G) : a * b = b * a

-- mul_assoc.{u_1} {G : Type u_1} [Semigroup G] (a b c : G) : a * b * c = a * (b * c)

-- which tells us that `mul_comm` takes two arguments and returns an
-- equality, and `mul_assoc` takes three arguments and returns an
-- equality.

-- So we can use this result from the library to prove what we want to prove

example (x y : ℕ) : x * y = y * x := mul_comm x y

-- you will also see this written using "tactics"

example (x y : ℕ) : x * y = y * x := by
  exact mul_comm x y

-- what if we wanted to prove something more complicated that just depended on this result?

-- for example, suppose we want to know that `z * x * y * w = z * y * x * w`

-- we can use the `rw` (rewrite) tactic which takes as argument an equality

example (x y z w : ℕ) : z * (x * y) * w = z * (y * x) * w := by  
   rw [mul_comm x y]


-- how would we avoid the awkwardness with the parentheses?
-- eliminating them depends on the associative law.

-- note that in Lean, the symbol * "associates to the left" which means that
-- `x * y * z` is just shorthand for `(x * y) * z`

example (x y z w : ℕ) : z * x * y * w = z * y * x * w := by  
   rw [mul_assoc z x y]
   rw [mul_assoc z y x]
   rw [mul_comm x y]

-- in this case, it is worth mentioning that the `ring` tactic can already close this goal
-- (and without any shenanigans with the parenthesis)

example (x y z w : ℕ) : z * x * y * w = z * y * x * w := by  
   ring

-- we can use hypotheses in our `rw` rewrites, as follows

 example (a b c d e : ℤ) (h: a * b = c * d) : a * b * e = c * d * e := by
   rw [ h ]

-- and we could have formulated that result as an implication  instead
-- you should read the symbol → as "implies" here

example (a b c d e : ℤ) : a * b = c * d →  a * b * e = c * d * e := by
   intro h
   rw [ h ]

-- the `linarith` tactic can prove equalities and inequalities arising from "linear arithmetic"

example (a b c : ℤ) (ha : a = 2) (h : a * b = a * c)  : b = c := by
   rw [ ha ] at h
   linarith


example (a b : ℝ) (h : 2*a ≤ b) (k : 1 ≤ a) : 2 ≤ b := by linarith

-- rewriting in a local assumption


example (a b c d : ℤ) (h : c = d*a + b) (h' : b = d) : c = d*a + d := by
  rw [h'] at h
  -- Our assumption `h` is now exactly what we have to prove
  exact h


-- you may need to use some of the following in the exercises below.

#check add_comm
#check add_mul
#check mul_add
#check add_mul

--------------------------------------------------------------------------------
-- exercises

-- 1.

example (x y z w  : ℤ) : x * y + x * z + x * w = x * (z + y + w) := by
  rw [ ← mul_add x y z ]


-- 2. 

example (a b c d : ℤ) (h : b = d + d) (h' : a = b + c) : a + b = c + 4 * d := by
  sorry


-- 3. 

-- formulate an `example` (as above) proving that if x and y are
-- integers and if x + y = 2, then x^2 + 2*x*y + y^2 = 4.

-- note that the `norm_num` tactic can settle numerical equalities like

example : 2*3 = 6 := by norm_num

example (x : ℤ) : x*x = x^2 := by 
  rw [ pow_two ]

-- 4.



--------------------------------------------------------------------------------


-- a ring is a type `R` which has an operation of addition and an
-- operation of multiplication on it.

-- 
