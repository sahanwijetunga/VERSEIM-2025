import Mathlib.Tactic

noncomputable section

open Module
open LinearMap
open LinearMap (BilinForm)

variable  {k V :Type} [Field k] 
  [AddCommGroup V] [Module k V] [Module.Finite k V]

set_option maxSynthPendingDepth 2 

#synth Ring (Module.End k (BilinForm k V))

example : Polynomial k := minpoly k (B := Module.End k (BilinForm k V)) lflip

example : Polynomial k := minpoly k (lflip:(BilinForm k V) →ₗ[k] (BilinForm k V))

def T : Module.End k (BilinForm k V) := lflip
def g : Polynomial k := minpoly k (B:=Module.End k (BilinForm k V)) T

example : Module.End k (BilinForm k V)  := Polynomial.aeval g T

