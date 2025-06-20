import Mathlib.Tactic

variable {a b : ℕ}
variable (h1 : a = b)

def foo : a = b := by exact h1 

example : a = b := by exact h1

theorem bar : a = b := by exact h1

theorem T : a = e := by
  calc
    a = b      := h1
    _ = c + 1  := h2
    _ = d + 1  := congrArg Nat.succ h3
    _ = 1 + d  := Nat.add_comm d 1
    _ = e      := Eq.symm h4
