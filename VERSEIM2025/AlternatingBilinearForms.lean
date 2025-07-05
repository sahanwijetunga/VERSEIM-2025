--------------------------------------------------------------------------------
/-
Copyright (c) 2025 Clea Bergsman, Katherine Buesing, George McNinch, Sahan Wijetunga. All rights reserved.

Released under the Apache 2.0 license as described in the file LICENSE.

VERSEIM-2025 REU @ Tufts University
-/

import Mathlib.Tactic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.QuadraticForm.Basic

import VERSEIM2025.HyperbolicBilinearForms

/- Sahan: The main results in this file should hold only for alternating forms.

  Major results (Completed):
  - ....
  Major results (Planned):
  - Any nondegenerate alternating bilinear form is hyperbolic
  - - Corollary: Nondegenerate alternating bilinear form is dimension 2
  - - Corollary: Nondegenerate alternating bilinear forms of equal dimension
      are isomorphic (as bilinear form spaces)
-/

namespace Alternating


variable {k V: Type*} [AddCommGroup V][Field k][Module k V]

variable {k V: Type*} [AddCommGroup V][Field k][Module k V]

open LinearMap (BilinForm)
open LinearMap.BilinForm
open BilinearForms -- This is the namespace in VERSEIM2025.Sahan.BilinearForms
open Hyperbolic -- This is the namespace in VERSEIM2025.HyperbolicBilinearForms

namespace Hidden


theorem hyp_pair_exists_alt {e: V} {β:BilinForm k V} (balt : IsAlt β) (hn: Nondegenerate β) (enz : e ≠ 0) :
  ∃ f, hyp_pair β e f := by
    have ⟨v, hv⟩ := exists_bilin_one enz hn
    use v
    constructor; . exact balt e
    constructor
    . exact balt v
    . exact hv

def hyp2_decomp_alt (β:BilinForm k V) [FiniteDimensional k V] (balt : IsAlt β) (e f : V) (h2:hyp_pair β e f)
  : orthog_direct_sum β (hypsubspace_two h2).toSubmodule :=
  orthog_decomp β (hypsubspace_two h2).toSubmodule (hyp2_nondeg_alt  β balt h2)

theorem alternating_is_hyperbolic_aux (B: BilinForm k V) (balt: IsAlt B) [FiniteDimensional k V]
(n: ℕ) (hn: n = Module.finrank k V): hypspace_pred B  := by
  induction' n using Nat.strong_induction_on with n h generalizing V
  case h =>
  match n with
  | 0 =>
    use PEmpty
    -- use (Module.finBasisOfFinrankEq k V hn.symm)
    -- constructor
    -- repeat intro i; contradiction
    sorry
  | 1 => sorry
  | k+2 => sorry

end Hidden

theorem foo: True := trivial

end Alternating
