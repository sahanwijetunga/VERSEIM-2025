import Mathlib.Tactic

variable {k : Type} [ Field k ]
variable {V : Type} [ AddCommGroup V ] [ Module k V ]

variable {ι:Type} [Fintype ι]

variable {b:Basis ι k V}

open LinearMap
open LinearMap (BilinForm)

def fun_two {X:Type*} (x y:X) : Fin 2 → X :=
  fun i => match i with
    | 0 => x
    | 1 => y

variable {β:BilinForm k V} (h:IsRefl β)


structure hyperbolic_two_space (β:BilinForm k V) (h:IsRefl β)
  (W:Submodule k V)  where
  e : V  
  f : V
  isotropic : β e e = 0 ∧ β f f = 0
  nondeg : (β: BilinForm k V) e f = 1
  lin_indep : LinearIndependent k (fun_two e f)
  span : W = Submodule.span k { e , f }
  
  
lemma symm_or_alt_of_reflexive (β:BilinForm k V) ( h : IsRefl β ): 
 IsSymm β ∨ IsAlt β := by
  
  have id₁ (x y z : V) : β x ( (β x y)• z - (β x z) • y ) = 0 := by calc 
    β x ( (β x y)• z - (β x z) • y) = (β x y) * (β x z) - (β x z) * ( β x y) := by simp
                                  _ = 0 := by ring

  have id₂ (x y z : V) : β ((β x y) • z - (β x z) • y) x = 0 := by 
    apply LinearMap.IsRefl.eq_zero h (id₁ x y z)

  have id₃ (x y z : V) : (β x y) * (β z x) = (β x z) * (β y x) := by
    suffices h : (β x y) * (β z x) - (β x z) * (β y x) = 0 by grind
    have : (β ((β x) y • z - (β x) z • y)) x = 0 := id₂ x y z
    rw [ β.sub_left ] at this
    rw [ β.smul_left, β.smul_left ] at this
    exact this

  have id₄ (x y : V) : (β x y)*(β x x) =  (β y x)*(β x x) := by
    rw [ id₃ x y x ] 
    ring

  

    



lemma hyp_is_nondeg (W:Submodule k V) (β:BilinForm k V) { h : IsRefl β } (hyp : hyperbolic_two_space β  h W) : 
  Nondegenerate (β.restrict W) := by 
    unfold Nondegenerate
  

example (a b  : k) (h: a - b = 0)  : a = b := by grind
