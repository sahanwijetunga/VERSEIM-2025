import Mathlib.Tactic
import Mathlib.Algebra.Polynomial.Module.Basic
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

open Polynomial 
open TensorProduct

noncomputable section

variable {R M: Type*} [CommRing R] [AddCommGroup M] [Module R M]

def poly_map (N:Type*) [AddCommGroup N] [Module R[X] N] 
   (f:M →ₗ[R] (ModuleCat.restrictScalars _ N)) : 
   PolynomialModule R M →ₗ[R[X]] N := by sorry

example (N:Type*) [AddCommGroup N] [Module R[X] N] : Module (R:Subring R[X]) N := inferInstance

example : Algebra R R[X] := inferInstance


def poly_mod_equiv_tensor_product  : PolynomialModule R M ≃ₗ[R[X]] R[X] ⊗[R] M  where
  toFun := by 
    unfold PolynomialModule 
    intro v 
    exact Finsupp.sum v (fun (n:ℕ) _ => (Polynomial.monomial n 1) ⊗ₜ (v n))
  map_add' := by 
    intro x y
    sorry
  map_smul' := by 
    intro f v
    sorry
  invFun := by sorry
  left_inv := by sorry
  right_inv := by sorry
