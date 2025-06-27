
import Mathlib.Tactic

import Mathlib.Data.FinEnum

#check FinEnum

-- THere are (at least) three different parts of Mathlib that define a
-- notion of cardinality.

-- Nat.card
-- Fintype.card
-- FinEnum.card

-- Sometimes (as below) we have to "convince" Lean that they are "the same".

-- FinEnum is nice enoguh to "keep track" of equivalences

-- there is automatically a `FinEnum` instance of the `Sum` of two
-- types with `FinEnum` instances. e.g.

example (n m :ℕ) : FinEnum ((Fin n) ⊕ (Fin m)) := inferInstance

-- here is how to get the cardinality from the FinEnum instance
example (X:Type) [FinEnum X] : ℕ := FinEnum.card X

-- and here is how to get the corresponding equivalence
example (X:Type) [FinEnum X] : X ≃ Fin (FinEnum.card X) := FinEnum.equiv

lemma card_eq_finenum_card (X:Type) [FinEnum X]  : Nat.card X = FinEnum.card X := by 
  rw [ Nat.card_eq_fintype_card ]
  exact Eq.symm FinEnum.card_eq_fintypeCard 

-- we need a lemma that says that the size of the `Sum` of `Fin n`s is
-- what it should be.  here I found a result stating that, but for
-- `Nat.card_sum`. Thus the need to compare the cardinalities

-- (this proof is perhaps a bit sloppy...)

lemma size_of_sum (n m : ℕ) : FinEnum.card ((Fin n) ⊕ (Fin m)) = n + m := by 
  have hn : n = FinEnum.card (Fin n) := Eq.symm FinEnum.card_fin 
  have hm : m = FinEnum.card (Fin m) := Eq.symm FinEnum.card_fin 
  apply Eq.symm
  nth_rw 1 [ hn , hm ]
  apply Eq.symm
  rw [ ← card_eq_finenum_card (Fin n), 
       ← card_eq_finenum_card (Fin m), 
       ← card_eq_finenum_card ((Fin n) ⊕ (Fin m)) ]
  apply Nat.card_sum 

-- now here we get the equivalence `(Fin n) ⊕ (Fin m) ≃ Fin (n+m)`
-- without much fuss.
 
example (n m : ℕ) : (Fin n) ⊕ (Fin m) ≃ Fin (n+m)  := by
   rw [ ← size_of_sum ]
   exact FinEnum.equiv
    

