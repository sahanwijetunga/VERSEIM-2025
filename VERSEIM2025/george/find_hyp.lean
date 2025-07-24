import Mathlib.Tactic

variable {k : Type} [ Field k ]
variable {V : Type} [ AddCommGroup V ] [ Module k V ]

variable {ι:Type} [Fintype ι]

variable {b:Basis ι k V}

open LinearMap
open LinearMap (BilinForm)

variable (β:BilinForm k V)

structure is_hyp_two (W:Submodule k V)  where
  
  
