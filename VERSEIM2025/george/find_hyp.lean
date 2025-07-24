import Mathlib.Tactic

variable {k : Type} [ Field k ]
variable {V : Type} [ AddCommGroup V ] [ Module k V ]

variable {ι:Type} [Fintype ι]

variable {b:Basis ι k V}

open LinearMap
open LinearMap (BilinForm)

variable {β:BilinForm k V} { h : IsRefl β } 

def fun_two {X:Type*} (x y:X) : Fin 2 → X :=
  fun i => match i with
    | 0 => x
    | 1 => y

structure hyperbolic_two_space (β:BilinForm k V) { h : IsRefl β } 
  (W:Submodule k V)  where
  e : V  
  f : V
  isotropic : β e e = 0 ∧ β f f = 0
  nondeg : β e f = 1
  lin_indep : LinearIndependent k (fun_two e f)
  span : W = Submodule.span k { e , f }
  
  
lemma hyp_is_nondeg (W:Submodule k V) (hyp : hyperbolic_two_space β W) : Nondegenerate β := by sorry
