import Mathlib.Tactic

open Module
open LinearMap
open LinearMap (BilinForm)

variable  {k V :Type} [Field k] 
  [AddCommGroup V] [Module k V] [Module.Finite k V]

set_option maxSynthPendingDepth 2 
#synth Ring (Module.End k (BilinForm k V))

abbrev bflip : Module.End k (BilinForm k V) := lflip

theorem symm_iff_eq_flip (β:BilinForm k V) : β.IsSymm ↔ β = bflip β := by sorry

theorem alt_iff_eq_neg_flip [Invertible (2:k)] (β:BilinForm k V) 
  : β.IsSymm ↔ β = -bflip β := by sorry

def SymmComp [Invertible (2:k)] (β:BilinForm k V) : BilinForm k V := 
  (1/2:k) • ( β + bflip β ) 

def AltComp [Invertible (2:k)] (β:BilinForm k V) : BilinForm k V := 
  (1/2:k) • ( β - bflip β)


theorem symm_comp_is_symm [Invertible (2:k)] (β:BilinForm k V) : β.IsSymm := by sorry

theorem symm_comp_is_alt [Invertible (2:k)] (β:BilinForm k V) : β.IsAlt := by sorry


theorem eq_add_symm_alt  [Invertible (2:k)] {β:BilinForm k V} :
  β = SymmComp β + AltComp β := by 
    unfold AltComp
    unfold SymmComp 
    sorry
