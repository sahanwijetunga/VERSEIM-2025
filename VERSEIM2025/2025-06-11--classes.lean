--------------------------------------------------------------------------------
/-
Copyright (c) 2025 George McNinch. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Author : George McNinch
-/

/- VERSEIM-2025 REU -/

import Mathlib.Tactic


structure two_simplex where
  x : ℚ
  y : ℚ 
  z : ℚ 
  x_nonneg : 0 ≤ x
  y_nonneg : 0 ≤ y
  z_nonneg : 0 ≤ z
  sum_eq : x + y + z = 1

def a : two_simplex where
  x := 1
  y := 0
  z := 0
  x_nonneg := by linarith
  y_nonneg := by linarith
  z_nonneg := by linarith
  sum_eq := by ring

#eval a

def swapXy (a : two_simplex) : two_simplex
    where
  x := a.y
  y := a.x
  z := a.z
  x_nonneg := a.y_nonneg
  y_nonneg := a.x_nonneg
  z_nonneg := a.z_nonneg
  sum_eq := by rw [add_comm a.y a.x] 
               rw [  a.sum_eq]

#eval swapXy a

--open BigOperators

structure StandardSimplex (n : ℕ) where
  V : Fin n → ℝ
  NonNeg : ∀ i : Fin n, 0 ≤ V i
  sum_eq_one : (∑ i, V i) = 1


namespace StandardSimplex

noncomputable
def midpt (n : ℕ) (a b : StandardSimplex n) : StandardSimplex n
    where
  V i := (a.V i + b.V i) / 2
  NonNeg := by
    intro i
    apply div_nonneg
    · linarith [a.NonNeg i, b.NonNeg i]
    norm_num
  sum_eq_one := by
    simp [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_add_distrib,
      a.sum_eq_one, b.sum_eq_one]
    field_simp

end StandardSimplex


--#check midpt 

#check StandardSimplex.midpt 

open StandardSimplex 

#check midpt 


--------------------------------------------------------------------------------

structure mygroup where
  carrier : Type
  mul : carrier → carrier → carrier 
  e : carrier
  
  identity_law_l (g:carrier) : mul e g = g
  identity_law_r  (g:carrier) : mul g e = g

  assoc ( g h k : carrier) : mul (mul g h) k = mul g (mul h k)

  inverse (g : carrier) : ∃ h, mul g h = e

structure Group₁ (α : Type*) where
  mul : α → α → α
  one : α
  inv : α → α
  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  mul_one : ∀ x : α, mul x one = x
  one_mul : ∀ x : α, mul one x = x
  inv_mul_cancel : ∀ x : α, mul (inv x) x = one

--- examples?

--------------------------------------------------------------------------------
-- e.g. "symmetric group on a set"

variable (α β γ : Type)

#check Equiv α β 
#check α ≃ β 

variable (f : α ≃ β) (g:β ≃ γ)

#check f.toFun 
#check f.invFun 

#check Equiv.refl 

#check f.right_inv 

#check Function.RightInverse 

#check f.left_inv  


-- want to view `Equiv α α` i.e. `α ≃ α` as a group.

#check (Equiv.refl α : α ≃ α)
#check (f.symm : β ≃ α)
#check (f.trans g : α ≃ γ)
#check Equiv.trans f g 

-- here is the goal

example : Group₁ (α ≃ α) := by sorry 

--  mul := Equiv.trans 


-- `Equiv.Perm α` is by definition `α ≃ α`.

def permGroup {α : Type*} : Group₁ (Equiv.Perm α)
    where
  mul f g := Equiv.trans g f
  one := Equiv.refl α
  inv := Equiv.symm
  mul_assoc f g h := (Equiv.trans_assoc _ _ _).symm
  one_mul := Equiv.trans_refl
  mul_one := Equiv.refl_trans
  inv_mul_cancel := Equiv.self_trans_symm

#check (@permGroup ℤ)


--------------------------------------------------------------------------------

-- can now prove statements about groups

example (α :Type) (G:Group₁ α) : ∀ x : α, G.mul x x = x → x = G.one := by 
  intro x h
  let y : α := G.inv x
  have k : G.mul y (G.mul x x) = G.mul y x :=  by rw [h]
  rw [←G.mul_assoc y x x] at k
  unfold y at k
  rw [G.inv_mul_cancel x] at k
  rw [G.one_mul] at k
  assumption


-- I got confused by this statement this afternoon -- the above proof
-- hypothesis `k` is the argument that Sahan suggested.  I think the
-- reason I got rattled is that I didn't think it all the way through
-- the point is that you do the `rw [h]` and then find an equality
-- that is definitionally true (i.e. true by `rfl`).


--------------------------------------------------------------------------------

-- an "programming" example for typeclasses

-- producing a "string representation function" for a type

-- there is actually already an existing such function, name reprStr

#eval reprStr (1/2 : ℚ)


class MyDisplay (α:Type) where
  mydisp : α → String

instance : MyDisplay two_simplex  where
  mydisp a := "< x:" ++ reprStr a.x ++ ", y:" ++ reprStr a.y ++ ", z:" ++ reprStr a.z ++ " >"


-- remember that `a:two_simplex`

#eval MyDisplay.mydisp a


-- in the type signature of a function, we can stipulate that a type
-- must have an instance of a some class, as in the following:

def doubleString {α:Type} [ MyDisplay α ] (a:α) : String := by
  open MyDisplay  in
  exact mydisp a ++ mydisp a 


-- notice that we can call doubleString on `a:two_simplex` since we
-- have defined a `MyDisplay` instance for `two_simplex

--#eval doubleString 
-- and I don't have to give any sort of argument to `doubleString`
-- confirming that this instance exists -- Lean *finds* the instance.


--------
-- another example

-- Lean has a typeclass for indicating that a Type is non-empty. That
-- typeclass is `Inhabited`

-- to create an instance for a type, you must indicate a `default`
-- element for the type.

-- for our simplex, we could choose a point to indicate that
-- `two_simplex` is non-empty:

instance : Inhabited two_simplex where
  default := by
    apply two_simplex.mk (1/3) (1/3) (1/3) 
    <;> linarith

#eval (Inhabited.default : two_simplex)

--------------------------------------------------------------------------------

-- group as typeclass rather than as a structure.

variable (G:Type) [Group G]

#check Group 

example ( x y : G) : G := x * y  -- Mul.mul x y 

example ( x : G) : x*1 = x := by group -- here 1 is the `one` term defined by the group structure 

--------------------------------------------------------------------------------

-- in Lean we need to consider also additive groups

variable (A : Type) [ aaa : AddGroup A ]

example ( a b c : A) : a + b + c = a + (b + c) :=  by
   rw [ add_assoc ]

--------------------------------------------------------------------------------

-- THis is how to say " let V be a vector space over k "

variable ( k : Type ) [ Field k ]


variable (V : Type) [AddCommGroup V ] [ Module k V ] 
