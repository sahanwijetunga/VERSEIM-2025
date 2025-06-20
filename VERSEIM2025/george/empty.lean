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
  

section test

variable (k V : Type) [Field k] [AddCommGroup V] [Module k V]

variable (β : V →ₗ[k] V →ₗ[k] k)


example (x y z : V) : β (x+y) z = β x z + β y z := by
  have h : β (x+y) = β x + β y := by exact LinearMap.map_add β x y
  have k : (β x + β y) z = β x z + β y z := rfl
  rw [ h,k ]

example (x y z : V) : β (x+y) z = β x z + β y z := LinearMap.BilinForm.add_left x y z


example (x y z : V) : β (x+y) z = β x z + β y z := by
  rw [ LinearMap.map_add β x y ]
  rfl

example (x y z : V) : β (x+y) z = β x z + β y z := by
  simp

end test


