--------------------------------------------------------------------------------
/-
Copyright (c) 2025 George McNinch. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Clea Bergsman, Katherine Buesing, George McNinch, Sahan Wijetunga
-/

/- VERSEIM-2025 REU -/

import Mathlib.Tactic

variable { k V : Type } [Field k] [AddCommGroup V] [Module k V]

-- possible new notation: `LinearMap.BilinForm k V` is the same thing
-- as `V →ₗ[k] V →ₗ[k] k`

-- indeed

example : (LinearMap.BilinForm k V) = (V →ₗ[k] V →ₗ[k] k) := rfl

-- (Having typed `V →ₗ[k] V →ₗ[k] k` several times, I now agree that
-- `BilinForm k V` is probably better notation...)

-- A matrix is a bit like a vector, with two index sets (one for
-- "rows" and one for "columns").

-- An n × m matrix has the following type

variable (n m:ℕ) in
#check Matrix (Fin n) (Fin m) k 


-- but more generally you could have a matrix whose rows and columns
-- are indexed by just any type (in our case, we'll typically insist
-- that those indexing types be finite!)

variable (rows cols : Type) [Fintype rows] [Fintype cols] in
#check Matrix rows cols k


-- the type of matrices has a vector space structure

example (n m:ℕ) : Module k (Matrix (Fin n) (Fin m) k) := inferInstance

example (rows cols : Type) : Module k (Matrix rows cols k) := inferInstance

-- if you want to construct explicit matrices, you can do so using
-- notation `!![ ... ]` with commas separating entries and semicolons
-- separating rows

#check !![ 1, 1; 0, (1:ℚ)]

-- and we can see the vector space struture in action:

#eval !![ 1, 1; 0, (1:ℚ)] + (2:ℚ)•!![1,2;0,-1]

-- You can even multiply matrices.

#eval !![ 1, 1; 0, (1:ℚ)] * !![ 1, 1; 0, (1:ℚ)]

-- (need for matrix multiplication is the reason for not representing
-- matrices simply as `Fin n → Fin m → k`).

-- given a matrix , you can get the ith row by evaluation, and the i j coefficient by evaluation:

#eval !![1,2,3;4,5,6] 1 

#eval !![1,2,3;4,5,6] 1 1

-- and finally you can take determinants:

example (a b : ℚ) : !![ a , 1 ; 0 , b ].det = a*b := by simp


-- on the black board, we have described how to get a matrix from a bilinear form β:
-- take a basis v₁, ... , vₙ of V and form the matrix whose i,j entrie is
-- `beta vᵢ vⱼ`

-- in fact, mathlib has implemented this construction via `BilinForm.toMatrix`


variable (β:LinearMap.BilinForm k V)
variable (b : Basis (Fin n) k V)

#check BilinForm.toMatrix b β

noncomputable example : Matrix (Fin n) (Fin n) k := BilinForm.toMatrix b β

-- more precisely, in the notation of the previous example,
-- `BilinForm.toMatrix b` is a linear equivalence:

#check LinearMap.BilinForm k V ≃ₗ[k] Matrix (Fin n) (Fin n) k

-- the mathlib theorem `BilinForm.toMatrix_apply` confirms that the
-- entries of the matrix correspond to the values of the bilinear form
-- at the corresponding basis vectors:

example (i j : Fin n) : (BilinForm.toMatrix b) β i j  = β (b i) (b j) := 
  BilinForm.toMatrix_apply b β i j

-- there is no need to only work with bases and rows/cols indexed by
-- `Fin`s (Note that the index type does need to have a `DecidableEq`
-- instance!)

variable (ι : Type) [Fintype ι] [DecidableEq ι]

variable (c : Basis ι k V)

-- using our basis `c` we'll construct an `ι × ι` matrix corresponding to `β`.

#check BilinForm.toMatrix c β

noncomputable example : Matrix ι ι k := BilinForm.toMatrix c β

-- we still know that the entries of the toMatrix are as indicated:

example (i j : ι) : (BilinForm.toMatrix c) β i j  = β (c i) (c j) := 
  BilinForm.toMatrix_apply c β i j


