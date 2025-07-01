import Mathlib.Tactic

variable (k V:Type) [Field k] [AddCommGroup V] [Module k V]

#check Basis 

variable (n : ℕ) (B : Basis (Fin n) k V)

variable (β : LinearMap.BilinForm k V)

#check BilinForm.toMatrix B


noncomputable example : Matrix (Fin n) (Fin n) k := BilinForm.toMatrix B β
 
 
