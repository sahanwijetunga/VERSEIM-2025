--------------------------------------------------------------------------------
/-
Copyright (c) 2025 Clea Bergsman, Katherine Buesing, George McNinch, Sahan Wijetunga. All rights reserved.

Released under the Apache 2.0 license as described in the file LICENSE.

VERSEIM-2025 REU @ Tufts University
-/

import Mathlib.Tactic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.QuadraticForm.Basic
-- import VERSEIM2025.HyperbolicBilinearForms --  File left not imported due to current work

/-
  The main results in this file should hold only for nondegenerate forms.

  Major results (Planned)
  - Any nondegenerate bilinear form is a direct sum of a hyperbolic
    space (see HyperbolicBilinearForms) and a definite space (∀x, β x x ≠ 0)

-/
