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

/- Sahan: The main results in this file should hold only for symmetric forms. -/


variable {k V: Type*} [AddCommGroup V][Field k][Module k V]

open LinearMap
open LinearMap (BilinForm)

-- Main result: symmetric bilinear form has orthogonal basis, from Mathlib
example {V : Type u} {K : Type v}
   [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
   [hK : Invertible (2: K)] {B : LinearMap.BilinForm K V} (hB₂ : IsSymm B) :
    ∃ (v : Basis (Fin (Module.finrank K V)) K V), IsOrthoᵢ B ⇑v := by
      exact LinearMap.BilinForm.exists_orthogonal_basis hB₂
