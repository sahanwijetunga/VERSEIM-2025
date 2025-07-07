--------------------------------------------------------------------------------
/-
Copyright (c) 2025 Clea Bergsman, Katherine Buesing, George McNinch, Sahan Wijetunga. All rights reserved.

Released under the Apache 2.0 license as described in the file LICENSE.

VERSEIM-2025 REU @ Tufts University
-/

-- import Mathlib.LinearAlgebra.QuadraticForm.Basic
-- import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import VERSEIM2025.OddHyperbolicForms

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

namespace Symmetric

variable {k V V': Type} [AddCommGroup V][AddCommGroup V'] [Field k] [Module k V] [Module k V']

open LinearMap (BilinForm)
open LinearMap.BilinForm
open BilinearForms -- This is the namespace in VERSEIM2025.Sahan.BilinearForms
open Hyperbolic -- This is the namespace in VERSEIM2025.HyperbolicBilinearForms
open BilinIsomorphisms -- This is the namespace in VERSEIM2025.BilinearFormIsomorphisms
open OddHyperbolic

-- symmetric bilinear form has orthogonal basis, from Mathlib
example {V : Type u} {K : Type v}
   [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
   [hK : Invertible (2: K)] {B : LinearMap.BilinForm K V} (hB₂ : IsSymm B) :
    ∃ (v : Basis (Fin (Module.finrank K V)) K V), LinearMap.IsOrthoᵢ B ⇑v := by
      exact LinearMap.BilinForm.exists_orthogonal_basis hB₂
-- TODO: Remove redundancy with Symmetric
lemma ex_nonzero (h: Module.finrank k V > 0) : ∃(v: V), v ≠ 0  := by
  contrapose! h
  suffices Module.finrank k V=0 from Nat.le_zero.mpr this
  refine Module.finrank_eq_zero_of_rank_eq_zero ?_
  exact rank_zero_iff_forall_zero.mpr h

structure AnisotropicSubspace (B: BilinForm k V) where
  submodule : Submodule k V
  pred : ∀ v ∈ submodule, (B v v = 0 → v=0)

-- def AnisotropicSubspaceZeroSpace (B: BilinForm k V) (h: ∀ (v: V), v = 0):
--   AnisotropicSubspace B := sorry

-- def GeneralizedHypspaceZeroSpace (B: BilinForm k V) (h: ∀ (v: V), v = 0):
--   GeneralizedHypspace B := sorry

structure FooSymm {B: BilinForm k V} (bsymm: IsSymm B) where
  orthog : GeneralizedHypsubspace B
  anisotropic : AnisotropicSubspace B
  compl : is_orthog_direct_sum B orthog.toSubmodule anisotropic.submodule

def ZeroHypSubspace (B: BilinForm k V): Hypsubspace B where
  I := Empty
  coe := fun _ ↦ 0
  linind := by
    exact linearIndependent_empty_type
  pred :=
    { isotropic_left := by exact fun i j ↦ zero_left 0,
      isotropic_right := by exact fun i j ↦ zero_left 0,
      orthog1 := by exact fun i j a ↦ zero_left 0,
      orthog2 := by exact fun i j a ↦ zero_left 0,
      unital_corr := by
        intro i
        contradiction
    }

def ZeroGeneralizedHypSubspace (B: BilinForm k V): GeneralizedHypsubspace B :=
  GeneralizedHypsubspace.even (ZeroHypSubspace B)


def FooSymm_of_GeneralizedHypspace {B: BilinForm k V} (bsymm: IsSymm B) (H: GeneralizedHypspace B):
  FooSymm bsymm := sorry

def FooSymm_of_anisotropic {B: BilinForm k V} {bsymm: IsSymm B} (h: ∀ v, (B v v = 0) → v=0):
  FooSymm bsymm := by sorry

noncomputable def FooSymmOfZeroSpace {B: BilinForm k V} (bsymm: IsSymm B) (h: ∀ (v: V), v = 0):
  FooSymm bsymm := by
  apply FooSymm_of_anisotropic
  exact fun v a ↦ h v

abbrev FooSymmPred {B: BilinForm k V} (bsymm: IsSymm B):= Nonempty (FooSymm bsymm)

theorem SymmRestrict {B: BilinForm k V} (bsymm: IsSymm B) (W: Submodule k V): IsSymm (B.restrict W) := by
  intro x y
  dsimp
  exact bsymm ↑x ↑y

def GeneralizedHypsubspaceExpand {B: BilinForm k V} (H: Hypsubspace B)
  (H': GeneralizedHypsubspace B) (orthog: OrthogSubspaces B H.toSubmodule H'.toSubmodule):
    GeneralizedHypsubspace B := sorry

theorem GeneralizedHypsubspaceExpand_Span  {B: BilinForm k V} (H: Hypsubspace B)
  (H': GeneralizedHypsubspace B) (orthog: OrthogSubspaces B H.toSubmodule H'.toSubmodule):
  (GeneralizedHypsubspaceExpand H H' orthog).toSubmodule = H.toSubmodule ⊔ H'.toSubmodule := sorry

def GeneralizedHypsubspaceRemoveFormRestriction {B: BilinForm k V} {W: Submodule k V}
  (H': GeneralizedHypsubspace (B.restrict W)) :
    GeneralizedHypsubspace B := sorry

theorem FooSymmPredExpand {B: BilinForm k V} (bsymm: IsSymm B) (H: Hypsubspace B)
  (horthog: orthog_direct_sum B (H.toSubmodule)) (hsymmpredorthog: FooSymmPred
  (SymmRestrict bsymm (B.orthogonal H.toSubmodule))):
  FooSymmPred bsymm := by
    have ⟨⟨orthog, anisotropic, compl⟩⟩ := hsymmpredorthog

    let W := (B.orthogonal H.toSubmodule)
    let U := anisotropic.submodule
    have orthog_new: GeneralizedHypsubspace B :=
      have horthogpartlynew: OrthogSubspaces B H.toSubmodule (GeneralizedHypsubspaceRemoveFormRestriction orthog).toSubmodule := sorry
      GeneralizedHypsubspaceExpand H (GeneralizedHypsubspaceRemoveFormRestriction orthog) horthogpartlynew
    have anisotropic_new: AnisotropicSubspace B :=
      {
      submodule := U.map W.subtype,
      pred := by
        rintro v h h'
        have ⟨u, huU, huv⟩ := Submodule.mem_map.mp h
        suffices u=0 from ?_
        . have: W.subtype u = 0 := by exact
          (AddSubmonoid.mk_eq_zero (B.orthogonal H.toSubmodule).toAddSubmonoid).mp this
          rw[<- huv,this]
        suffices B (W.subtype u) (W.subtype u) = 0 from ?_
        . apply anisotropic.pred
          . exact huU
          rw[<- this]
          simp
        rw[huv]
        exact h'
      }
    have compl_new: is_orthog_direct_sum B orthog_new.toSubmodule anisotropic_new.submodule := by
      constructor
      . sorry
      . have := bsymm.isRefl
        refine OrthogSubspaces_of_OrthogSubspacesWeak_refl ?_ this
        rintro ⟨x,hx⟩  y
        sorry
    exact Nonempty.intro
      { orthog := orthog_new, anisotropic := anisotropic_new, compl := compl_new }

-- Note: exists_smul_eq_of_finrank_eq_one
theorem OneDimIsOddHypspace (B: BilinForm k V) (hrank: Module.finrank k V = 1):
  Nonempty (OddHypspace B) := by
    let Heven: Hypsubspace B := ZeroHypSubspace B
    have EmptyHevenBasisIndex: IsEmpty (Heven.I ⊕ Heven.I) := by
      have: IsEmpty Heven.I := by
        have: Heven.I = Empty := by
          unfold Heven
          simp[ZeroHypSubspace]
        rw[this]
        exact Empty.instIsEmpty
      exact instIsEmptySum
    have b: Basis ((Heven.I ⊕ Heven.I) ⊕ singleton) k V := by
      have c: Basis singleton k V := by
        exact Module.basisUnique Hyperbolic.singleton hrank
      have iso: (Heven.I ⊕ Heven.I) ⊕ singleton ≃ singleton := by
        exact Equiv.emptySum (Heven.I ⊕ Heven.I) Hyperbolic.singleton
      exact c.reindex (id iso.symm)
    have compatible : Heven.coe = b ∘ Sum.inl := by
      ext i
      exfalso
      exact IsEmpty.false i
    have H: OddHypspace B := { hyp := Heven, basis := b, compatible := compatible }
    exact Nonempty.intro H


-- Note: exists_smul_eq_of_finrank_eq_one
theorem OneDimIsGeneralizedHypspace (B: BilinForm k V)  (hrank: Module.finrank k V = 1) :
  Nonempty (GeneralizedHypspace B) := by
    have ⟨H⟩  := OneDimIsOddHypspace B hrank
    constructor
    exact GeneralizedHypspace.odd H


-- Note: exists_smul_eq_of_finrank_eq_one
theorem OneDimIsFooSymm {B: BilinForm k V} (bsymm: IsSymm B) (hrank: Module.finrank k V = 1):
  FooSymmPred bsymm := by
  have ⟨H⟩ := OneDimIsGeneralizedHypspace B hrank
  have: FooSymm bsymm := FooSymm_of_GeneralizedHypspace bsymm H
  unfold FooSymmPred
  exact Nonempty.intro this

protected theorem symmetric_is_FooSymmPred_aux (p: ℕ)  (B: BilinForm k V) (bsymm: IsSymm B) [FiniteDimensional k V]
(n: ℕ) (hn: n = Module.finrank k V) (hd: B.Nondegenerate) [CharP k p] (hn2 : p ≠ 2): FooSymmPred bsymm  := by
  induction' n using Nat.strong_induction_on with n h generalizing V
  have hr : IsRefl B := IsSymm.isRefl bsymm
  case h =>
  match n with
  | 0 =>
    have: ∀ (v: V), v = 0 := by
      symm at hn
      exact finrank_zero_iff_forall_zero.mp hn
    exact Nonempty.intro (FooSymmOfZeroSpace bsymm this)
  | 1 =>
    have: Module.finrank k V = 1 := by exact id (Eq.symm hn)
    exact OneDimIsFooSymm bsymm this
  | m+2 =>
    by_cases h':(∃ (e: V), e ≠ 0 ∧ B e e =0)
    . have ⟨e, he_nonzero, he_isotropic⟩ := h'
      let ⟨f, hef⟩ := hyp_pair_exists_symm p bsymm hd he_nonzero he_isotropic hn2
      let H : Hypsubspace B := Hypsubspace_two hef
      let W' := B.orthogonal H.toSubmodule
      have hHW' : is_orthog_direct_sum B H.toSubmodule W' := hyp2_decomp_refl B hr hef
      have hpredW' : FooSymmPred (SymmRestrict bsymm W') := by
        have hmm2: m < m+2 := Nat.lt_add_of_pos_right (Nat.zero_lt_two)
        have hbW'IsGoodProp: (B.restrict W').IsSymm := fun x ↦ fun y ↦ bsymm (W'.subtype x) (W'.subtype y)
        have hIsComplW'H: IsCompl H.toSubmodule W' := by
            exact BilinearForms.isCompl_orthogonal_of_restrict_nondegenerate B H.toSubmodule
              (hyp2_nondeg_refl B (hr) hef)
        have hWrankeqm: m = Module.finrank k ↥W' := by
          have: Module.finrank k ↥W' + Module.finrank k H.toSubmodule = Module.finrank k V := by
            rw[add_comm]
            exact Submodule.finrank_add_eq_of_isCompl hIsComplW'H
          rw[Hypsubspace_two_finrank_2,<- hn] at this
          exact (Nat.add_right_cancel this).symm
        have hBW'Nondegenerate: (B.restrict W').Nondegenerate := by
          apply (restrict_nondegenerate_iff_isCompl_orthogonal hr).mpr
          rw[orthogonal_orthogonal hd (hr) H.toSubmodule]
          exact id (IsCompl.symm hIsComplW'H)
        exact h m hmm2 (B.restrict W') hbW'IsGoodProp hWrankeqm hBW'Nondegenerate
      exact FooSymmPredExpand bsymm H hHW' hpredW'
    . have: ∀ (v: V), (B v v = 0 → v=0) := by
        intro v h
        contrapose! h'
        use v
      constructor
      exact FooSymm_of_anisotropic this

noncomputable def FooSymm_of_FooSymmPred {B: BilinForm k V} {bsymm: IsSymm B} (h: FooSymmPred bsymm): FooSymm bsymm := by
    apply Classical.choice
    have ⟨H⟩ := h
    constructor
    exact H

noncomputable def symmetric_is_FooSymm  (p: ℕ)  {B: BilinForm k V} (bsymm: IsSymm B) (hd: B.Nondegenerate) [FiniteDimensional k V]
  [CharP k p] (hn2 : p ≠ 2):
  FooSymm bsymm :=
    FooSymm_of_FooSymmPred <| Symmetric.symmetric_is_FooSymmPred_aux p B bsymm (Module.finrank k V) rfl hd hn2


end Symmetric
