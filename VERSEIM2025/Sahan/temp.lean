--------------------------------------------------------------------------------
/-
Copyright (c) 2025 Clea Bergsman, Katherine Buesing, George McNinch, Sahan Wijetunga. All rights reserved.

Released under the Apache 2.0 license as described in the file LICENSE.

VERSEIM-2025 REU @ Tufts University
-/

import Mathlib.Tactic
import Mathlib.Algebra.Polynomial.Module.Basic
import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.LinearAlgebra.QuadraticForm.Isometry
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.TensorProduct.Basic

open scoped Polynomial

variable {I F V V': Type*} [Field F][AddCommGroup V] [AddCommGroup V'] [Module F V][Module F V']

variable (b : Basis I F V) (b': Basis I F V')

example: V ≃ₗ[F] V' := b.repr.trans b'.repr.symm

example (a: F[X]): RatFunc F := by
    let foo: RatFunc F := algebraMap _ _ a
    simp at foo
    sorry
