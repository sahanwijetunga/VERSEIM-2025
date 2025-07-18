import Mathlib.Tactic

variable {k:Type} [Field k]

variable {ι:Type} [Fintype ι] [DecidableEq ι]

-- a predicate `p:ι → Prop` defines a subtype of ι. In order to know
-- that subtype is finite, apparently Lean/Mathlib needs a decidable
-- instance on the values of p

variable {p:ι → Prop} [(i:ι) → Decidable (p i)]

-- you could also write `[DecidablePred p]` instead of 
-- `[(i:ι) → Decidable (p i)]`

-- the notation `{ i // p i }` i.e. `{ i∶ι // p i }` is the *subtype*
-- determined by p, rather than the subset. SO: subtype uses `//`
-- while subset uses `|`.  Roughly: the subtype is just "the subset
-- determined by p, viewed as a type"

example : Fintype { i // p i } := inferInstance

-- we can formulate "two block" matrices using the predicate `p : ι →
-- Prop`

-- we can extract the "p is true" block as follows

example (M:Matrix ι ι k) (p:ι→Prop) : Matrix { i // p i } {i // p i } k :=
  Matrix.toSquareBlockProp M p

-- and e.g. we can get the "p is false" block via

example (M:Matrix ι ι k) : Matrix { i // ¬ p i } {i // ¬ p i } k :=
  Matrix.toSquareBlockProp M (fun i => ¬ (p i))

-- M is "block upper triangular" if `¬ p i ∧ p j → M i j = 0`

-- lean knows via `Matrix.twoBlockTriangular_det` that for a block
-- upper triangular matrix, the determinant is the product of the
-- determinants of the blocks:

example (M:Matrix ι ι k) 
  (h : ∀ (i : ι), ¬p i → ∀ (j : ι), p j → M i j = 0)
  : M.det = (Matrix.toSquareBlockProp M p).det * 
            (Matrix.toSquareBlockProp M (fun i => ¬ p i)).det := 
  Matrix.twoBlockTriangular_det M p h


-- on the other hand, M is "block lower triangular" if `p i ∧ ¬ p j →
-- M i j = 0`

-- there is of course a similar determinant product result for lower
-- triangular matrices, mysteriously named `Matrix.twoBlockTriangular_det'`

example (M:Matrix ι ι k) 
  (h : ∀ (i : ι), p i → ∀ (j : ι), ¬ p j → M i j = 0)
  : M.det = (Matrix.toSquareBlockProp M p).det * 
            (Matrix.toSquareBlockProp M (fun i => ¬ p i)).det := 
  Matrix.twoBlockTriangular_det' M p h


-- there are of course also not-necessarily-square blocks of M. (THe
-- lower/upper triangular assumption means that one of these blocks is
-- the zero matrix.)

-- here are those blocks:
 
def lower_block (M:Matrix ι ι k) (p:ι → Prop) [DecidablePred p]: Matrix { i // p i} {i // ¬ p i } k :=
  Matrix.of fun i j => M i j

def upper_block (M:Matrix ι ι k) (p:ι → Prop) [DecidablePred p]: Matrix { i // ¬ p i} {i // p i } k :=
  Matrix.of fun i j => M i j

-- we could rephrase the assumptions of the determinant result as follows:

example (M:Matrix ι ι k) 
  (h : upper_block M p = 0)
  : M.det = (Matrix.toSquareBlockProp M p).det * 
            (Matrix.toSquareBlockProp M (fun i => ¬ p i)).det := by
  have hh : ∀ (i : ι), p i → ∀ (j : ι), ¬ p j → M i j = 0 := by
   unfold upper_block at h
   intro i hi j hj
   rw [ ← Matrix.of_apply h i j ]  
  exact Matrix.twoBlockTriangular_det' M p hh

example (M:Matrix ι ι k ) : Matrix ι ι k := 0
