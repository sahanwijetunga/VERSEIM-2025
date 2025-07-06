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

  Major results (Mostly Completed)
  - Any nondegenerate alternating bilinear form is hyperbolic (`alternating_is_hyperbolic_aux`)
    - *Base cases are not proved yet*; Inductive step has been proved
    - Corollary: Nondegenerate alternating bilinear form is dimension 2n (`alternate_is_even_dimension`)
  - - Corollary: Nondegenerate alternating bilinear forms of equal (finite) dimension
      are isomorphic (as bilinear form spaces)  (`alternate_iso`)

  Major results (Planned - Aspirational):
  - Remove the [FiniteDimensional k V] requirement from `alternating_is_hyperbolic` (if possible).
    - Proof Sketch:
      - Increasing limit of hyperbolic spaces is hyperbolic *(May be wrong)*
        - This would require (at minimum) that if W is a finite dimensional subspace
          which V is Nondegenerate on then W + Wᗮ = V.
      - Any maximal hyperbolic space must be the entire space
    - Hence also generalize `alternate_iso` to not require finite dimensional
-/

namespace Alternating


variable {k V V': Type} [AddCommGroup V][AddCommGroup V'] [Field k] [Module k V] [Module k V']


open LinearMap (BilinForm)
open LinearMap.BilinForm
open BilinearForms -- This is the namespace in VERSEIM2025.Sahan.BilinearForms
open Hyperbolic -- This is the namespace in VERSEIM2025.HyperbolicBilinearForms
open BilinIsomorphisms -- This is the namespace in VERSEIM2025.BilinearFormIsomorphisms


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

-- Clean up proof?
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
  | 1 => sorry -- proof should be done by proving false from hd
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


noncomputable def alternating_is_hyperbolic {B: BilinForm k V} (balt: IsAlt B) (hd: B.Nondegenerate) [FiniteDimensional k V]:
  (I: Type) × (hypspace B I) :=
    hypspace_of_hypspace_pred <| Alternating.alternating_is_hyperbolic_aux B balt (Module.finrank k V) rfl hd

theorem alternate_is_even_dimension {B: BilinForm k V} (balt: IsAlt B) (hd: B.Nondegenerate) [FiniteDimensional k V]:
  Even (Module.finrank k V) := (alternating_is_hyperbolic balt hd).2.is_even_dimension

theorem alternate_is_even_dimension' {B: BilinForm k V} (balt: IsAlt B) (hd: B.Nondegenerate):
  Even (Module.rank k V) := by
  by_cases FiniteDimensional k V
  . have h := alternate_is_even_dimension balt hd
    suffices Module.finrank k V = Module.rank k V from ?_
    . let ⟨r,hr⟩ := h
      rw[<- this]
      use r
      simp[hr]
    exact Module.finrank_eq_rank k V
  . have ⟨s, ⟨b⟩ ⟩ := Basis.exists_basis k V
    have: Module.rank k V = Cardinal.mk s := by exact Eq.symm (Basis.mk_eq_rank'' b)
    rw[this]
    have: Cardinal.aleph0 ≤ Cardinal.mk s := by
      refine Cardinal.infinite_iff.mp ?_
      refine not_finite_iff_infinite.mp ?_
      intro h
      have: FiniteDimensional k V := by exact Module.Finite.of_basis b
      contradiction
    use (Cardinal.mk s)
    exact Eq.symm (Cardinal.add_eq_self this)

noncomputable def alternate_iso {B: BilinForm k V} {B': BilinForm k V'} (balt: IsAlt B) (b'alt: IsAlt B')
  (hd: B.Nondegenerate) (hd': B'.Nondegenerate) [FiniteDimensional k V] [FiniteDimensional k V']
  (h: Module.finrank k V = Module.finrank k V'): EquivBilin B B' := by
    let ⟨I, H⟩ := alternating_is_hyperbolic balt hd
    let ⟨I', H'⟩ := alternating_is_hyperbolic b'alt hd'
    apply H.iso_from_iso_index H'
    case π => exact iso_index_from_rank_eq H H' h
    intro i
    let i' := iso_index_from_rank_eq H H' h i
    show (B (H.basis (Sum.inr i))) (H.basis (Sum.inl i)) =
      (B' (H'.basis (Sum.inr i')) (H'.basis (Sum.inl i')))
    let bskew := skew_of_alt B balt
    let b'skew := skew_of_alt B' b'alt
    rw[bskew]
    rw[b'skew]
    simp

end Alternating
