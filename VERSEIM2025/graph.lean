import Mathlib.Tactic

variable { α : Type} 

variable { k : Type } [Field k]

noncomputable
example ( a : Set α) [p:Finite a] : Finset α := Set.Finite.toFinset p



def ev : { x : ℕ // Nat.mod x 2 = 0 } := 
  ⟨ 248 , by simp ⟩



example (a:Set α) : Type := ↥a


example : Set ℕ := { x : ℕ | Nat.mod x 2 = 0 }
