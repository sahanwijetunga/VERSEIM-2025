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

example (n : ℕ) : n = n := by rfl 

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

example (x y z w : ℕ) : z * x * y * w = z * y * w * x := by  
   ring

-- we can use hypotheses in our `rw` rewrites, as follows

 example (a b d e : ℤ) (h: b * e = d * e) : a * b * e = a * d * e := by
   rw [ mul_assoc a b e, mul_assoc a d e]
   rw [ h ]

-- and we could have formulated that result as an implication  instead
-- you should read the symbol → as "implies" here

example (a b c d e : ℤ) : a * b = c * d →  a * b * e = c * d * e := by
   intro h
   rw [ h ]

-- the `linarith` tactic can prove equalities and inequalities arising from "linear arithmetic"

example (a b c : ℤ) (ha : a = 2) (h : a * b = a * c)  : b = c := by
   rw [ ha ] at h
   --refine Int.neg_inj.mp ?_
   linarith

example (a b : ℝ) (h : a  + 2 = b + 2) : a =b := 
  by linarith 


example (a b : ℝ) (h : 2*a ≤ b) (k : 1 ≤ a) : 2 ≤ b := by linarith

-- rewriting in a local assumption


example (a b c d : ℤ) (h : c = d*a + b) (h' : b = d) : c = d*a + d := by
  rw [h'] at h
  -- Our assumption `h` is now exactly what we have to prove
  -- exact h
  assumption 

-- you may need to use some of the following in the exercises below.

#check add_comm
#check add_mul
#check mul_add

--------------------------------------------------------------------------------
-- exercises

-- 1.

example (x y z w  : ℤ) : x * y + x * z + x * w = x * (z + y + w) := by sorry


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
  -- exact Eq.symm (Lean.Grind.Semiring.pow_two x)


-- here is a possible solution
#check two_mul

example ( x y :ℤ) (h: x+y = 2) : x^2 + 2*x*y + y^2 = 4 := by
have k  : x^2 + 2*x*y + y^2 = (x+y)*(x+y) := by 
  rw [ mul_add, add_mul ]
  rw [ pow_two, pow_two ]
  rw [ add_mul ]
  rw [ mul_comm y x ]
  rw [ add_assoc (x*x) (x*y) _ ]
  rw [ ← add_assoc (x*y) (x*y) ]
  rw [ ← two_mul ]
  rw [ ← mul_assoc 2 x y]
  exact add_assoc (x*x) (2*x*y) _
rw [ k , h]
norm_num

--------------------------------------------------------------------------------
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by rw [mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by rw [← add_assoc, add_assoc (a * a)]
    _ = a * a + 2 * (a * b) + b * b := by rw [mul_comm b a, ← two_mul]

--------------------------------------------------------------------------------

variable (x y z :ℤ)


example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  exact dvd_mul_left x _

def f : ℤ → ℤ → ℤ := by
  intro x y
  exact x^2 + y^2

#check f

#eval f 1 2 

-- f 1 is really ℤ → ℤ  via y |--> f 1 y

lemma foobar (x:ℕ) : x ∣ x ^ 2 := by
  apply dvd_mul_left

example : 4 ∣ 4^2 := foobar 4
