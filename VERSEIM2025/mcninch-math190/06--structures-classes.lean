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
-- 06 -- Structures and Classes
--------------------------------------------------------------------------------

-- # Structures 

/- a structure is a specification of a collection of data, possibly
with constraints that the data is required to satisfy. An instance of
the structure is a particular bundle of data satisfying the
constraints.  -/

@[ext]
structure LatticePoint where
  x : ℤ
  y : ℤ
  z : ℤ
  deriving Repr

-- the `@[ext]` bit is there so that `Lean` produces Theorems which
-- will allows us to conclude equality between `LatticePoint`s by
-- extensionality.

#check LatticePoint.ext  --   `⊢ ∀ (x y : LatticePoint), x.x = y.x → x.y = y.y → x.z = y.z → x = y`

example (a b : LatticePoint) (hx:a.x = b.x) (hy:a.y= b.y) (hz:a.z = b.z) : a = b := by 
  ext 
  repeat 
    assumption
  done

def lp1 : LatticePoint where
  x := 1
  y := -2
  z := 3


#print lp1
#check lp1.x

-- other ways of creation

def lp2 : LatticePoint :=
  LatticePoint.mk 2 4 6
-- or ⟨2,4,6⟩

-- `LatticePoint.mk` is the name of the *constructor* 

#check lp2

def degree (l:LatticePoint) : ℤ :=
  l.x + l.y + l.z

#check degree

#eval degree lp1



def diagonal (a:ℤ) : LatticePoint :=
  LatticePoint.mk a a a

#eval (diagonal 3)

example (a:ℤ) : degree (diagonal a) = 3*a := by
  rw [ degree ]
  rw [ diagonal ]
  simp
  -- or just do `show a+a+a = 3*a` instead of the previous 3 lines
  group


namespace LatticePoint

def add (a b : LatticePoint) : LatticePoint :=
  ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩
-- or
-- mk (a.x + b.x) (a.y + b.y) (a.z + b.z)


#eval add lp1 lp2


#eval lp1.add lp2

#eval add (diagonal 3) (diagonal 4)



-- "degree is a group homomorphism"
example (a b : LatticePoint) : degree ( LatticePoint.add a b ) = degree a + degree b := by
  rw [ add ]
  rw [ degree, degree, degree]
  simp  -- after simplifying, this is just an equation in ℤ, which we
        -- can confirm using results for (additive) `group`s
  group
  

-- can define add using "pattern matching"

def addAlt : LatticePoint → LatticePoint → LatticePoint
  | mk x₁ y₁ z₁, mk x₂ y₂ z₂ => ⟨x₁ + x₂, y₁ + y₂, z₁ + z₂⟩


def add_assoc : ∀ x y z : LatticePoint, add (add x y) z = add x (add y z) := by
  intro x y z 
  rw [ add , add , add, add]
  simp
  group -- just uses facts about the additve group ℤ
  trivial
  done

def zero : LatticePoint := diagonal 0

def neg : LatticePoint → LatticePoint 
  | mk x y z => ⟨-x, -y, -z⟩

def add_zero : ∀ x : LatticePoint, add x zero = x := by
  intro x
  rw [add, zero, diagonal ]
  simp
  
def zero_add : ∀ x : LatticePoint, add zero x = x := by
  intro x
  rw [ add, zero, diagonal ]
  simp

def add_left_neg : ∀ x : LatticePoint, add (neg x) x = zero := by
  intro x
  rw [ add, neg , zero ]
  simp
  rfl

def add_comm : ∀ x y : LatticePoint, add x y = add y x := by
  intro x y
  rw [ add , add ]
  simp
  group -- just uses facts about the additve group ℤ
  trivial

end LatticePoint

-- Next steps: link addition of LatticePoints to the `+` symbol (!)

-- # simplex as a structure

open BigOperators

structure StandardSimplex (n : ℕ) where
  V : Fin n → ℝ
  NonNeg : ∀ i : Fin n, 0 ≤ V i
  sum_eq_one : (∑ i, V i) = 1


-- Here `Fin n` is a type that has exacly `n` terms, for `n:ℕ`.
-- `BigOperators` allows you to sum over `Fin n`.

-- here a term of type `StandardSimple n` is a *point* `V` in the simples,
-- so the point `V` has n coordinates, each of which is a real number ≥0,
-- and the sum of all coordinates `V i` is equal to 1.

-- Let's define an operation for finding the *midpoint* of the line
-- segment between two points in a simplex

noncomputable section

def midpoint' (n : ℕ) (a b : StandardSimplex n) : StandardSimplex n
  where
  V i := (a.V i + b.V i) / 2
  -- or
  --V := λ i => (a.V i + b.V i)
  NonNeg := by
    intro i
    apply div_nonneg
    · linarith [a.NonNeg i, b.NonNeg i]
    · norm_num
  sum_eq_one := by
    simp [ div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_add_distrib,
      a.sum_eq_one, b.sum_eq_one]
    field_simp

end


-- # Algebraic Structures



-- Let's define the structure of an *addtive* group
-- I'm including commutativity here, though I don't think `MathLib` does

structure AddGroup₁ (α : Type*) where
  add : α → α → α
  zero : α
  neg : α → α
  add_assoc : ∀ x y z : α, add (add x y) z = add x (add y z)
  add_zero : ∀ x : α, add x zero = x
  zero_add : ∀ x : α, add zero x = x
  add_left_neg : ∀ x : α, add (neg x) x = zero 
  add_comm : ∀ x y : α, add x y = add y x

-- since `α` is a *parameter* in the definition of `AddGroup₁`, 
-- you should think of a term `g : AddGroup₁ α` as being an *additive group structure on `α`*

-- we often write `G` for a type that is the carrier type for a group


-- for example, our `LatticePoint` type may be given the structure of a group:

def LatticeGroup : AddGroup₁ LatticePoint where
  add := LatticePoint.add
  zero := LatticePoint.zero
  neg := LatticePoint.neg
  add_assoc := LatticePoint.add_assoc
  add_zero := LatticePoint.add_zero
  zero_add := LatticePoint.zero_add
  add_left_neg := LatticePoint.add_left_neg
  add_comm := LatticePoint.add_comm

--------------------------------------------------------------------------------

-- we are going to rewrite the structure above in order to enable nicer notation and other things...


class AddGroup₂ (α : Type*) where
  add : α → α → α
  zero : α
  neg : α → α
  add_assoc : ∀ x y z : α, add (add x y) z = add x (add y z)
  add_zero : ∀ x : α, add x zero = x
  zero_add : ∀ x : α, add zero x = x
  add_left_neg : ∀ x : α, add (neg x) x = zero 
  add_comm : ∀ x y : α, add x y = add y x

instance : AddGroup₂ LatticePoint  where
  add := LatticePoint.add
  zero := LatticePoint.zero
  neg := LatticePoint.neg
  add_assoc := LatticePoint.add_assoc
  add_zero := LatticePoint.add_zero
  zero_add := LatticePoint.zero_add
  add_left_neg := LatticePoint.add_left_neg
  add_comm := LatticePoint.add_comm


-- Lean already has an `Add` class

instance : Add LatticePoint where
  add := LatticePoint.add

-- and Lean has a `Neg` class

instance : Neg LatticePoint where
  neg := LatticePoint.neg

instance : Sub LatticePoint where
  sub a b := a + -b

instance : Zero LatticePoint where
  zero := LatticePoint.zero

-- with this *magic* we can now use symbols `+`, `-` and `0` for the additve group `LatticePoint`

example (a b: LatticePoint) : LatticePoint := a + b

#eval lp1 + lp2

#eval lp1 - lp2

#eval lp1 + 0


-- let's prove that `add_right_neg` always holds for `AddGroup₂ α`

section 
open AddGroup₂
theorem add_right_neg' {A:Type} [AddGroup₂ A] (a:A) : add a (neg a) = zero := by
  rw [add_comm a (neg a)]
  apply AddGroup₂.add_left_neg

end 

-- and now as a consequence, we can use `add_right_neg'` for `LatticePoint` group

example (a : LatticePoint) : a - a = 0 := by
  exact add_right_neg' a


--- finally, we really ought to have first defined the `Add`, `Zero`, `Sub`, `Neg` instances,
--- and then defined `AddGroup` to `extend` these

-- then we can use additive notation in the "group laws"

class AddGroup₃ (α : Type*) extends Add α, Neg α, Sub α, Zero α where
--  add : α → α → α
--  zero : α
--  neg : α → α
  add_assoc : ∀ x y z : α, (x+y)+z = x + (y+z)
  add_zero : ∀ x : α, x + 0 = x
  zero_add : ∀ x : α, 0 + x = x
  add_left_neg : ∀ x : α, -x + x = 0
  add_comm : ∀ x y : α, x + y = y + x



