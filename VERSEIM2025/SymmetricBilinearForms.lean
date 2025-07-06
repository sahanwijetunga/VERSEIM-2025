--------------------------------------------------------------------------------
/-
Copyright (c) 2025 Clea Bergsman, Katherine Buesing, George McNinch, Sahan Wijetunga. All rights reserved.

Released under the Apache 2.0 license as described in the file LICENSE.

VERSEIM-2025 REU @ Tufts University
-/

import Mathlib.Tactic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import VERSEIM2025.Sahan.BilinearForms

/-
  The main results in this file should hold only for symmetric forms.

  Major results (Completed):
  - Symmetric bilinear form has orthogonal basis (from Mathlib)

  Major results (Planned):
  - Any nondegenerate symmetric bilinear form is the direct sum of a
    hyperbolic and anisotropic (definite) form (or the direct sum of that +
    a one dim subspace)
  - - Technically could be a corollary from NonDegenerateBilinearForms.lean
      but should be easier to prove here first

  Major results (Planned - Aspirational!) (These are listed in arbitrary order, and may not be correct)
  - Isomorphism classes of nondegenerate symmetric bilinear forms
  - Let the psuedo rank of a symmetric bilinear form be the maximal dimension
    of any anisotropic (definite) subspace. Prove that any two symmetric bilinear forms
    with the same dimension and psuedo rank are isomorphic.
  - Prove some sort of uniqueness of the hyperbolic + anisotropic (definite) decomposition
  - - I do not know if the subspaces are unique; if not then (if possible)
      prove if the dimensions are at least invariant.
 -/


variable {k V: Type*} [AddCommGroup V][Field k][Module k V]

open LinearMap (BilinForm)
open LinearMap.BilinForm
open BilinearForms -- This is the namespace in VERSEIM2025.Sahan.BilinearForms

-- Main result: symmetric bilinear form has orthogonal basis, from Mathlib
example {V : Type u} {K : Type v}
   [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
   [hK : Invertible (2: K)] {B : LinearMap.BilinForm K V} (hB₂ : IsSymm B) :
    ∃ (v : Basis (Fin (Module.finrank K V)) K V), LinearMap.IsOrthoᵢ B ⇑v := by
      exact LinearMap.BilinForm.exists_orthogonal_basis hB₂
