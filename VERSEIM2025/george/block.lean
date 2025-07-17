import Mathlib.Tactic

noncomputable section

variable {k:Type} [Field k]

variable {ι:Type} [Fintype ι] [DecidableEq ι]

example (ι:Type) [Fintype ι] (p:ι → Prop) [(i:ι) → Decidable (p i)] : Fintype { i // p i } := inferInstance

-- we can formulate block matrices using a predicate `p : ι → Prop`

-- we can extract the "p is true" block as follows

example (M:Matrix ι ι k) (p:ι→Prop) : Matrix { i // p i } {i // p i } k :=
  Matrix.toSquareBlockProp M p

-- and e.g. we can get the "p is false" block via

example (M:Matrix ι ι k) (p:ι→Prop) : Matrix { i // ¬ p i } {i // ¬ p i } k :=
  Matrix.toSquareBlockProp M (fun i => ¬ (p i))


-- M is "block upper triangular" if `¬ p i ∧ p j → M i j = 0`


example (M:Matrix ι ι k) (p:ι→Prop) 
  (h : ∀ (i : ι), ¬p i → ∀ (j : ι), p j → M i j = 0)
  : M.det = (Matrix.toSquareBlockProp M p).det * 
            (Matrix.toSquareBlockProp m (fun i => ¬ p i)).det := by sorry
