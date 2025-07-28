--------------------------------------------------------------------------------
/-
Copyright (c) 2025 Clea Bergsman, Katherine Buesing, George McNinch, Sahan Wijetunga. All rights reserved.

Released under the Apache 2.0 license as described in the file LICENSE.

VERSEIM-2025 REU @ Tufts University
-/

import VERSEIM2025.Forms.RationalFunctionFields.CasselsPfister

namespace RationalFunctionFields

open scoped Polynomial
open scoped TensorProduct
open scoped PolynomialModule
open CasselsPfister

variable {F: Type*} [Field F]

theorem sum_squares (f: F[X]) {n: ℕ} {l: Fin n → F(X)} (hlf: f = ∑ i, l i * l i):
    ∃ l': Fin n → F[X], f = ∑ i, l' i * l' i := sorry



end RationalFunctionFields
