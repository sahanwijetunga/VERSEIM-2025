--------------------------------------------------------------------------------
/-
Copyright (c) 2025 Clea Bergsman, Katherine Buesing, George McNinch, Sahan Wijetunga. All rights reserved.

Released under the Apache 2.0 license as described in the file LICENSE.

VERSEIM-2025 REU @ Tufts University
-/

import Mathlib.Tactic
import Mathlib.Algebra.Polynomial.Module.Basic
import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct

namespace CasselsPfister

open Polynomial
open scoped TensorProduct

variable {F V: Type} [Field F] [AddCommGroup V] [Module F V]

example:= PolynomialModule F V

example:= F[X] ⊗[F] V

#check TensorProduct

variable (foo: F[X])

theorem FooSummWork {α}(v w: α →₀ V) (g : α → V →+ V):
  (v+w).sum (fun a => fun v => g a v) = (v.sum (fun a => fun v => g a v)) + (w.sum (fun a => fun v => g a v)) := by
    exact Finsupp.sum_hom_add_index g

-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/TensorProduct/MvPolynomial.html#MvPolynomial.rTensor
--  is relevant (but does things in multivariable polynomials)
noncomputable def PolynomialEquiv: PolynomialModule F V ≃ₗ[F[X]] F[X] ⊗[F] V := sorry


/-- Agrees with Polynomial notion of degree. -/
def PolynomialModule_degree (v: PolynomialModule F V): WithBot ℕ :=  v.support.max

example (p: F[X]): p.degree = p.support.max := rfl

noncomputable abbrev TensorPolynomialModule_degree (v: F[X] ⊗[F] V): WithBot ℕ :=PolynomialModule_degree (PolynomialEquiv.invFun v)

noncomputable example (a: F): F[X] := Polynomial.C a


protected lemma CasselsPfister_GetSmallerDegree (f: F[X]) (u r: PolynomialModule F V) (hf: f.degree > 0): True := sorry

end CasselsPfister
