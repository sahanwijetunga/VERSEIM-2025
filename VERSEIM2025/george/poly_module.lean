import Mathlib.Tactic
import Mathlib.Algebra.Polynomial.Module.Basic
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

open Polynomial 
open TensorProduct

noncomputable section

variable {R M: Type*} [CommRing R] [AddCommGroup M] [Module R M]

variable {N:Type*} [AddCommGroup N] [Module R[X] N] [Module R N] [ IsScalarTower R R[X] N]

def poly_map (f:M →ₗ[R] N) : PolynomialModule R M →ₗ[R[X]] N where
  toFun := by
    intro v
    unfold PolynomialModule at v
    exact Finsupp.sum v (fun (n:ℕ) _ => (Polynomial.monomial n (1:R)) • (f (v n)))
  map_add' := by 
    intro x y
    sorry
  map_smul' := by
    intro m x
    sorry

-- inclusion of `M` into `PolynomialModule R M` is an R-module homomorphism

def const_incl : M →ₗ[R] PolynomialModule R M where
  toFun := fun m => Finsupp.single 0 m
  map_add' := by simp
  map_smul' := by sorry


def poly_mod_equiv_tensor_product  : PolynomialModule R M ≃ₗ[R[X]] R[X] ⊗[R] M  where
  toFun := (poly_map const_incl).toFun
  map_add' := (poly_map const_incl).map_add
  map_smul' := (poly_map const_incl).map_smul
  invFun := by sorry
  left_inv := by sorry
  right_inv := by sorry
