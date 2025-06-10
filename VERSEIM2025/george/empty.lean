import Mathlib.Tactic

def option_to_string : Option String → String :=
  fun os =>
    match os with
    | some s => s
    | none => "<<nothing>>"

#eval option_to_string (some "foo")

#eval option_to_string none


example : ({ 1, 1, 2 }:Set ℕ) = ({ 1, 2 }:Set ℕ) := by
  ext
  

