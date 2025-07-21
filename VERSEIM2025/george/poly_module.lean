import Mathlib.Tactic
import Mathlib.Algebra.Polynomial.Module.Basic
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

open Polynomial 
open TensorProduct

noncomputable section

variable {R M:Type} [CommRing R] [AddCommGroup M] [Module R M] 

/-- 
For a polynomial `f:R[X]`, and an R-module M, multiplication
by f determines an R-module homomorphism `M →ₗ[R] PolynomialModule R M`
--/
@[simp]
def mul_by_poly 
  (f:R[X]) : M →ₗ[R] PolynomialModule R M where
  toFun := fun m => f • (PolynomialModule.single R 0 m)
  map_add' := by simp
  map_smul' := by 
    intro t m
    rw [ PolynomialModule.single_smul ]
    rw [ smul_comm ]
    simp only [RingHom.id_apply]
    
/--
There is a bilinear mapping `R[X] →ₗ[R] M →ₗ[R] PolynomialModule R M`
given by the rule `f ↦ m ↦ (mul_by_poly f) m`
--/
@[simp]
def bmap (R M:Type) [CommRing R] [AddCommGroup M] [Module R M] : 
   R[X] →ₗ[R] M →ₗ[R] PolynomialModule R M where
   toFun := by 
     intro f
     apply mul_by_poly f
   map_add' := by 
     intro f g
     ext
     simp only [mul_by_poly, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
     exact  add_smul f g _
   map_smul' := by 
     intro t f
     ext
     simp only [mul_by_poly, smul_assoc, LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply,
                LinearMap.smul_apply ]

/-- 
There is a `R[X]`-linear mapping `R[X] ⊗[R] M → PolynomialModule R M`
determined (via `TensorProduct.lift`) by the bilinear mapping `bmap`

The mapping property of the tensor product gives the underyling
`R`-linear mapping, which is then confirmed (using
`TensorProduct.induction_on`) to be `R[X]`-linear.
--/
@[simp]
def tensor_map (R M:Type) [CommRing R] [AddCommGroup M] [Module R M]  : 
  R[X] ⊗[R] M →ₗ[R[X]] PolynomialModule R M := by
  let φ : R[X] ⊗[R] M →ₗ[R] PolynomialModule R M := lift (bmap R M)
  exact 
    { toFun := φ.toFun,
      map_add' := φ.map_add,
      map_smul' := by 
        intro g x
        simp
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul h y => 
            unfold φ
            rw [ smul_tmul', lift.tmul, lift.tmul , smul_eq_mul ]
            simp only [bmap, mul_by_poly, LinearMap.coe_mk, AddHom.coe_mk]
            rw [ ←smul_eq_mul, smul_assoc ] 
        | add x y hx hy => 
            rw [ smul_add, map_add, map_add, smul_add ]
            rw [ hx ,hy ]        
    }


example : IsScalarTower R R[X] (PolynomialModule R M) := inferInstance

lemma pm_sum_single_index {N:Type} [AddCommGroup N] [Module R N] {m:ℕ} {y:M} 
  {g:ℕ → M → N} (hg : g m 0 = 0): 
  Finsupp.sum ((PolynomialModule.single R m) y) g = g m y :=  by
  apply Finsupp.sum_single_index
  · exact hg

def poly_mod_equiv_tensor_product  : (R[X] ⊗[R] M) ≃ₗ[R[X]] (PolynomialModule R M) := by
 let incl : ℕ → M →+ R[X] ⊗[R] M := by
   intro n
   exact 
    {
      toFun := fun x => monomial n 1 ⊗ₜ[R] x
      map_zero' := by simp
      map_add' m₁ m₂ := tmul_add _ m₁ m₂
    }

    
 let ψ : PolynomialModule R M →+ R[X] ⊗[R] M := 
    {
     toFun := fun v => v.sum fun n => (incl n).toFun 
     map_zero' := by simp
     map_add' := (Finsupp.liftAddHom incl).map_add
    }

 exact
 { toFun := (tensor_map R M).toFun

   map_add' := (tensor_map R M).map_add

   map_smul' := (tensor_map R M).map_smul

   invFun := ψ

   left_inv := by 
     unfold Function.LeftInverse
     intro x
     induction x using TensorProduct.induction_on with
     | zero => simp
     | tmul h y  => 
        simp only [tensor_map, bmap, mul_by_poly, 
                   AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
                   AddHom.coe_mk, lift.tmul, LinearMap.coe_mk
                   ] 
        induction h using Polynomial.induction_on' with
        | add p q hp hq => 
           rw [ add_smul ]
           unfold ψ; simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
           unfold ψ at hp; simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk] at hp
           unfold ψ at hq; simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk] at hq
           rw [ Finsupp.sum_add_index (h_zero := by simp) ]
           · rw [ hp, hq ] 
             rw [ add_tmul ]
           · intro _ _ b₁ b₂  
             exact tmul_add _ b₁ b₂
        | monomial m t => 
           rw [ PolynomialModule.monomial_smul_single  ] 
           simp only [add_zero]
           unfold ψ; simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk] 
           rw [ pm_sum_single_index ( hg := by apply tmul_zero ) ]
           simp [ incl ]
           sorry
           -- #check smul_assoc ((monomial m) 1) t (1 ⊗ₜ[R] y : R[X] ⊗[R] M)
           -- rw [ ←]
           -- --rw [ ←TensorProduct.smul_tmul ]
           -- simp only [smul_eq_C_mul t, C_mul_monomial, mul_one]
     
     | add w₁ w₂ hw₁ hw₂ => 
        rw [ (tensor_map R M).map_add' w₁ w₂ ]
        rw [ ψ.map_add ]
        rw [ hw₁, hw₂ ]
       
   right_inv := by sorry
   }

example (f:ℕ →₀ ℝ) (g:ℕ →₀ ℝ) (h:f = g) : 
  Finsupp.sum f (fun _ r => r) = Finsupp.sum g (fun _ r => r) :=
  by rw [ h]


