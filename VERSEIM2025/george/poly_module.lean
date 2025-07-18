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


def const_incl : M →ₗ[R] PolynomialModule R M where
  toFun := _
  map_add' := _
  map_smul' := _


def poly_mod_equiv_tensor_product  : PolynomialModule R M ≃ₗ[R[X]] R[X] ⊗[R] M  where
  toFun := (poly_map _).toFun
  map_add' := (poly_map _).map_add
  map_smul' := (poly_map _).map_smul
  invFun := by sorry
  left_inv := by sorry
  right_inv := by sorry
