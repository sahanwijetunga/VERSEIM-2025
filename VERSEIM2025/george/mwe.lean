import Mathlib.Tactic
import Mathlib.LinearAlgebra.Charpoly.Basic

open Module
open LinearMap
open LinearMap (BilinForm)

variable  {k V :Type} [Field k] 
  [AddCommGroup V] [Module k V] [Module.Finite k V]

example : Ring (Module.End k V) := inferInstance       

example : Ring (Module.End k (BilinForm k V)) := inferInstance -- fails

example : Algebra k (Module.End k (BilinForm k V)) := inferInstance -- succeeds?!

example : Polynomial k := minpoly k (B := Module.End k (BilinForm k V)) lflip

-- minpoly example reports "failed to synthesize
--                          Ring (End k (BilinForm k V)) "


-- also fails, but maybe less surprising
example : Polynomial k := minpoly k (lflip:(BilinForm k V) →ₗ[k] (BilinForm k V))

