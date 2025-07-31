import Mathlib.Tactic

noncomputable section

open Module
open LinearMap
open LinearMap (BilinForm)

variable  {k V :Type} [CommRing k] [NeZero (1:k)] [AddCommGroup V] [Module k V] 
   [Module.Finite k V] [Invertible (2:k)]
     
example : NeZero (1:k) := inferInstance  


     
example ( a b : k ) (h:2*a = 2*b) : a = b:= by 
  have : (2:k) ≠ 0 := by exact two_ne_zero
  simp_all
  
example ( v w : V ) (h:(2:k)•v = (2:k)•w) : v = w := by 
  have : (2:k) ≠ 0 := by exact two_ne_zero  
  
