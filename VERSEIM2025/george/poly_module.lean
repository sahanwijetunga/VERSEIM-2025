import Mathlib.Tactic
import Mathlib.Algebra.Polynomial.Module.Basic
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

open Polynomial 
open TensorProduct

noncomputable section

variable {R M: Type*} [CommRing R] [AddCommGroup M] [Module R M]

variable {N:Type*} [AddCommGroup N] [Module R[X] N] [Module R N] 
                   [IsScalarTower R R[X] N]

def poly_map (f:M →ₗ[R] N) : PolynomialModule R M →ₗ[R[X]] N where
  toFun :=  fun v => 
    v.sum  fun (n:ℕ) _ => (Polynomial.monomial n (1:R)) • f (v n)
  map_add' := by 
    intro x y
    have (x y : PolynomialModule R M) (n:ℕ): f ((x + y) n) = f (x n) + f (y n) := by
      rw [PolynomialModule.add_apply R x y n]
      simp
    rw [ this x y ]
    --sorry
  map_smul' := by
    intro m x
    sorry

example (f:ℕ →₀ ℤ) (g:ℕ →₀ ℤ) (h:(n:ℕ) → f n = g n) :
  Finsupp.sum f (fun n _ => f n) = Finsupp.sum g (fun n _ => g n)  := by 
  rw [h]



-- inclusion of `M` into `PolynomialModule R M` is an R-module
-- homomorphism it is important to use PolynomialModule.single rather
-- than FinSupp.single here, to get easy proofs for map_add and
-- map_smul
def const_incl : M →ₗ[R] PolynomialModule R M where
  toFun := PolynomialModule.single R 0
  map_add' :=  by simp only [ map_add, implies_true ]
  map_smul' := PolynomialModule.single_smul R 0 

def poly_mod_equiv_tensor_product  : PolynomialModule R M ≃ₗ[R[X]] R[X] ⊗[R] M  where
  toFun := (poly_map const_incl).toFun
  map_add' := (poly_map const_incl).map_add
  map_smul' := by
    intro f m
    simp
    (poly_map const_incl).map_smul 
  invFun := by sorry
  left_inv := by sorry
  right_inv := by sorry
