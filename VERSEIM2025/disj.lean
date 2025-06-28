
import Mathlib.Tactic

import Mathlib.Data.FinEnum

-- THere are (at least) four different parts of Mathlib that define a
-- notion of cardinality.


-- Nat.card
-- Fintype.card
-- FinEnum.card
-- Finset.card

-- Sometimes (as below) we have to "convince" Lean that they are "the same".

-- We are going to give several proofs below of the fact that there is
-- an equivalence `(Fin n) ⊕ (Fin m) ≃ Fin (n+m)`

--------------------------------------------------------------------------------
-- I. via Fintype

lemma card_fin_sum_fin (n m : ℕ) : Fintype.card ((Fin n) ⊕ (Fin m)) = n + m := by simp

-- just by knowing the cardinality, we get an (abstract, noncomputable) equivalence!

noncomputable def ft_equiv (n m : ℕ) : (Fin n) ⊕ (Fin m) ≃ Fin (n+m)  := by
  apply Fintype.equivOfCardEq 
  rw [Fintype.card_sum]
  rw [Fintype.card_fin n]
  rw [Fintype.card_fin m]
  rw [Fintype.card_fin (n+m)]


-- the main tools are `Fintype.card_sum` which states

-- theorem Fintype.card_sum {α : Type u_1} {β : Type u_2} [Fintype α] [Fintype β] :
--   card (α ⊕ β) = card α + card β

-- and

-- noncomputable def Fintype.equivOfCardEq {α : Type u_1} {β : Type u_2} [Fintype α] [Fintype β] 
--   (h : card α = card β) :
--   α ≃ β

-- but we can't compute with the def `ft_equiv`:  these evals throw errors...

-- #eval (ft_equiv 10 10).toFun (Sum.inl 0) 
-- #eval (ft_equiv 10 10).toFun (Sum.inr 0) 


--------------------------------------------------------------------------------
-- II. proof via `FinEnum`

-- `FinEnum` "keeps track" of equivalences. More precisely, if

-- `(X : Type) [Finset X]` and if the cardinality of X is n, then the
-- typeclass instance gives a specified(!) equivalence of types `X ≃
-- Fin n`.

-- there is automatically a `FinEnum` instance of the `Sum` of two
-- types with `FinEnum` instances. e.g.

example (n m :ℕ) : FinEnum ((Fin n) ⊕ (Fin m)) := inferInstance

-- here is how to get the cardinality from the FinEnum instance
example (X:Type) [FinEnum X] : ℕ := FinEnum.card X

-- and here is how to get the corresponding equivalence
example (X:Type) [FinEnum X] (n:ℕ) (h:n = FinEnum.card X) : X ≃ Fin n := by
  rw [h]
  exact FinEnum.equiv

-- with `FinEnum`, we don't have the "noncomputable" restriction on
-- the equivalence:
 
def fe_equi (n m : ℕ) : (Fin n) ⊕ (Fin m) ≃ Fin (n+m)  := by
   rw [← card_fin_sum_fin ]
   rw [← FinEnum.card_eq_fintypeCard ]
   exact FinEnum.equiv
    
-- now we can see what choices Lean made in defining this equivalence!
-- for example:

#eval (fe_equi 5 7).toFun (Sum.inl 0) -- (0:Fin 12)
#eval (fe_equi 5 7).toFun (Sum.inr 0) -- (5:Fin 12)
#eval (fe_equi 5 7).toFun (Sum.inr 6) -- (11:Fin 12)
