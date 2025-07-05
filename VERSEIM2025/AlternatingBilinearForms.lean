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

/-
  The main results in this file should hold only for alternating forms.

  Major results (Completed):
  - ....
  Major results (Planned):
  - Any nondegenerate alternating bilinear form is hyperbolic
  - - Corollary: Nondegenerate alternating bilinear form is dimension 2
  - - Corollary: Nondegenerate alternating bilinear forms of equal dimension
      are isomorphic (as bilinear form spaces)
-/

namespace Alternating


variable {k V: Type} [AddCommGroup V][Field k][Module k V]

variable {k V: Type} [AddCommGroup V][Field k][Module k V]

open LinearMap (BilinForm)
open LinearMap.BilinForm
open BilinearForms -- This is the namespace in VERSEIM2025.Sahan.BilinearForms
open Hyperbolic -- This is the namespace in VERSEIM2025.HyperbolicBilinearForms

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

#check hypspace_of_orthog_direct_sum

lemma ex_nonzero (h: Module.finrank k V > 0) : ∃(v: V), v ≠ 0  := by
  contrapose! h
  suffices Module.finrank k V=0 from Nat.le_zero.mpr this
  refine Module.finrank_eq_zero_of_rank_eq_zero ?_
  exact rank_zero_iff_forall_zero.mpr h

protected theorem alternating_is_hyperbolic_aux (B: BilinForm k V) (balt: IsAlt B) [FiniteDimensional k V]
(n: ℕ) (hn: n = Module.finrank k V) (hd: B.Nondegenerate): hypspace_pred B  := by
  induction' n using Nat.strong_induction_on with n h generalizing V
  case h =>
  match n with
  | 0 =>
    use Empty
    -- use (Module.finBasisOfFinrankEq k V hn.symm)
    -- constructor
    -- repeat intro i; contradiction
    sorry -- note Module.finrank_eq_rank'
  | 1 => sorry
  | m+2 =>
    have: ∃ (e: V), e ≠ 0 := by
      have: m+2 > 0 := by exact Nat.zero_lt_succ (m + 1)
      rw[hn] at this
      exact ex_nonzero this
    let ⟨e, he⟩ := this
    let ⟨f, hef⟩ := hyp_pair_exists_alt balt hd he
    let H : hypsubspace B singleton := hypsubspace_two hef
    let W' := B.orthogonal H.toSubmodule
    have hHW' : is_orthog_direct_sum B H.toSubmodule W' := hyp2_decomp_alt B balt e f hef

    have hpredW' : hypspace_pred (B.restrict W') := by
      have hmm2: m < m+2 := Nat.lt_add_of_pos_right (Nat.zero_lt_two)
      have hbW'IsAlt: (B.restrict W').IsAlt := fun x ↦ balt (W'.subtype x)
      have hIsComplW'H: IsCompl W' H.toSubmodule := by
          refine
            IsCompl.symm
              (BilinearForms.isCompl_orthogonal_of_restrict_nondegenerate B H.toSubmodule ?_)
          exact hyp2_nondeg_alt B balt hef
      have hWrankeqm: m = Module.finrank k ↥W' := by
        have: Module.finrank k ↥W' + Module.finrank k H.toSubmodule = Module.finrank k V := by
          exact Submodule.finrank_add_eq_of_isCompl hIsComplW'H
        rw[hypsubspace_two_finrank_2] at this
        rw[<- hn] at this
        symm
        exact Nat.add_right_cancel this
      have hBW'Nondegenerate: (B.restrict W').Nondegenerate := by
        refine (restrict_nondegenerate_iff_isCompl_orthogonal (IsAlt.isRefl balt)).mpr ?_
        have: B.orthogonal W' = H.toSubmodule := by
          exact orthogonal_orthogonal hd (IsAlt.isRefl balt) H.toSubmodule
        rw[this]
        exact hIsComplW'H
      exact h m hmm2 (B.restrict W') hbW'IsAlt hWrankeqm hBW'Nondegenerate

    have ⟨I,H', hH'W'⟩ := hypsubspace_of_hypspace_pred_restrict hpredW'

    have h: is_orthog_direct_sum B H.toSubmodule H'.toSubmodule := by
      simp_all

    apply hypspace_pred_of_hypspace (hypspace_of_orthog_direct_sum h)


theorem alternating_is_hyperbolic (B: BilinForm k V) (balt: IsAlt B) (hd: B.Nondegenerate) [FiniteDimensional k V]:
  hypspace_pred B := Alternating.alternating_is_hyperbolic_aux B balt (Module.finrank k V) rfl hd

end Alternating
