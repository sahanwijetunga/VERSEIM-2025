import Mathlib.Tactic
import Mathlib.LinearAlgebra.Charpoly.Basic

open Module
open LinearMap
open LinearMap (BilinForm)


variable  {k V :Type} [Field k]
  [AddCommGroup V] [Module k V] [Module.Finite k V]

example : Ring (Module.End k V) := inferInstance       -- baseline; this succeeds

example : Semiring   (Module.End k (BilinForm k V)) := inferInstance -- succeed
example : Ring   (Module.End k V) := inferInstance -- succeed

example : Ring   (Module.End k (BilinForm k V)) := inferInstance -- fail
example : Ring   (Module.End k (BilinForm k V)) := Module.End.instRing (R := k) (N₁ := BilinForm k V)

example : Algebra k (Module.End k (BilinForm k V)) := inferInstance -- succeeds?!

example : Polynomial k := minpoly k (B := Module.End k (BilinForm k V)) lflip

-- minpoly example reports "failed to synthesize
--                          Ring (End k (BilinForm k V)) "


-- the following also fails, but maybe that is less surprising
example : Polynomial k := minpoly k (lflip:(BilinForm k V) →ₗ[k] (BilinForm k V))
