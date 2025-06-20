import Mathlib.Tactic

open BigOperators

def f (n:ℕ) : Fin n → Nat := Fin.toNat

#eval @f 3 

def sum_n (n:ℕ) : ℕ := ∑ i:Fin n, (f n) i

theorem sum_n_eq_expr (n:ℕ) : sum_n n = n*(n+1)/2 := by 
  unfold sum_n
  unfold f
  induction n with
  | zero => rfl 
  | succ => sorry


