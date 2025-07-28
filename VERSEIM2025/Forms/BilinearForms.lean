--------------------------------------------------------------------------------
/-
Copyright (c) 2025 Clea Bergsman, Katherine Buesing, George McNinch, Sahan Wijetunga. All rights reserved.

Released under the Apache 2.0 license as described in the file LICENSE.

VERSEIM-2025 REU @ Tufts University
-/

import Mathlib.Tactic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

namespace BilinearForms

variable { k V : Type* } [Field k] [ AddCommGroup V ]  [Module k V]

-- let's use the MathLib notions for Bilinear forms

open LinearMap (BilinForm)
open LinearMap.BilinForm

-- then we haves

example : (V →ₗ[k] V →ₗ[k] k) = (BilinForm k V) := rfl

#check LinearMap.BilinForm.IsAlt
#check LinearMap.BilinForm.IsSymm

-- Sahan: Is there no Mathlib version? I couldn't find any
def Skew (β:BilinForm k V) : Prop :=
  ∀ v w : V, β v w = - β w v

-- a bilinear form is said to be reflexive if `∀ x y, β x y = 0 → β y
-- x = 0`.


lemma skew_of_alt (β:BilinForm k V) (ha : IsAlt β) :
  Skew β := by
  intro v w
  have h0 : β (v+w) = β v + β w := by simp
  have h : β (v+w) (v+w) = (β v) v + (β w) v + (β v) w + (β w) w :=
    calc
    (β (v+w)) (v+w) = (β v) (v+w) + (β w) (v+w) := by rw [LinearMap.BilinForm.add_left]
    _ = (β v) v + (β w) v + (β v) w + (β w) w := by
      rw [LinearMap.BilinForm.add_right v v w, LinearMap.BilinForm.add_right w v w, ← add_assoc]; ring
  have hv : β v v = 0 := by apply ha
  have hw : β w w = 0 := by apply ha
  have hvw : β (v+w) (v+w) = 0 := by apply ha
  rw [hv, hw, hvw, zero_add, add_zero, add_comm] at h
  have h1: 0 + -(β w) v = (β v) w + (β w) v + -(β w) v := by
    apply (@add_right_cancel_iff _ _ _ (-(β w) v) 0 ((β v) w + (β w) v)).mpr h
  rw [zero_add] at h1
  rw [← sub_eq_add_neg] at h1
  rw [← add_sub ((β v) w) ((β w) v) ((β w) v)] at h1
  rw [sub_self ((β w) v)] at h1
  rw [add_zero] at h1
  symm at h1
  exact h1


-- the next lemma says that for a vector space over a field k of
-- characteristic different from 2, for v in V the equation `2v=0`
-- implies that `v=0`.


lemma eq_zero_of_two_mul_eq_zero  { k : Type* } [ Field k]
  [CharZero k] (x:k) (h:2*x = 0) : x = 0 := by
  --have nz2_inst : NeZero ↑2 := inferInstance
  have nz2 : (2:k) ≠ 0 := NeZero.ne ↑2
  by_contra x_neq_zero
  have two_mul_ne_zero : ↑2*x ≠ 0 :=
    mul_ne_zero nz2 x_neq_zero
  exact two_mul_ne_zero h


lemma eq_zero_of_two_mul_eq_zero' { k : Type* } [ Field k]
  {p:ℕ} [CharP k p] [ hn2:Fact (p≠2)]
  (x:k) (h:2*x = 0) : x = 0 := by
    have ring_char_n2 : ringChar k ≠ 2 := by
       rw [ ringChar.eq k p ]
       exact Fact.elim hn2
    have two_neq_zero : (2:k) ≠ 0 := by
       apply Ring.two_ne_zero ring_char_n2
    by_contra x_neq_zero
    have two_mul_ne_zero : (↑2:k) * x ≠ 0 :=
       mul_ne_zero two_neq_zero x_neq_zero
    exact two_mul_ne_zero h


example (x:ℝ) (h:2*x = 0) : x=0 := eq_zero_of_two_mul_eq_zero x h

lemma eq_zero_of_two_mul_eq_zero_vector (k: Type*) { V : Type* }
  [ Field k] [ AddCommGroup V]
  [Module k V] {p:ℕ} [CharP k p] (hn2 : p ≠ 2)
  (v:V) (h:2•v = 0) : v = 0 := by
    have two_smul_eq_zero : (2:k) • v = 0 := by
      rw [ ofNat_smul_eq_nsmul k 2 v ]
      assumption
    have ring_char_n2 : ringChar k ≠ 2 := by
       rw [ ringChar.eq k p ]
       assumption
    have two_neq_zero : (2:k) ≠ 0 := by
       apply Ring.two_ne_zero ring_char_n2
    by_contra v_neq_zero
    have two_smul_ne_zero : (↑2:k) • v ≠ 0 :=
       smul_ne_zero two_neq_zero v_neq_zero
    exact two_smul_ne_zero two_smul_eq_zero

lemma zero_of_two_mul_eq_zero  { k : Type* } [ Field k]
  [NeZero (2: k)] (x:k) (h:2*x = 0) : x = 0 := by
  have nz2_inst : NeZero ↑2 := inferInstance
  have nz2 : (2:k) ≠ 0 := NeZero.ne ↑2
  by_contra x_neq_zero
  have two_mul_ne_zero : ↑2*x ≠ 0 :=
    mul_ne_zero nz2 x_neq_zero
  exact two_mul_ne_zero h

lemma alt_iff_skew (β:V →ₗ[k] V →ₗ[k] k)
  [NeZero (2: k)]: IsAlt β ↔ Skew β := by
  constructor
  . intro ha
    apply skew_of_alt _ ha
  intro hs
  intro v
  have h1 : β v v = -β v v := by apply hs
  have h2 : β v v + β v v = β v v + -β v v := by
    apply (@add_left_cancel_iff _ _ _ (β v v) (β v v) (-β v v)).mpr  h1
  rw [← sub_eq_add_neg, sub_self ((β v) v)] at h2
  rw [← two_mul] at h2

  exact zero_of_two_mul_eq_zero _ h2

-- REMARK: we are really only interested in the case of forms which
-- are either alternating or symmetric.  We are going to formulate a
-- number of predicates on forms which in the general case (of a form
-- which is neither alternating nor symmetric) should have a more
-- complicated definition.

-- ===============
-- Reflexive forms
-- ===============

-- Mathlib has a predicate for reflexive forms -- namely
-- `LinearMap.IsRefl`. So it might be useful if we record that our
-- alternating and symmetric forms are reflexive.

lemma skew_is_reflexive (β:BilinForm k V) (h:Skew β) : IsRefl β := by
  intro v w l
  rw [h]
  simp
  assumption

lemma alt_is_reflexive (β:BilinForm k V) (h:IsAlt β) : IsRefl β := by
  intro v w l
  have hv : β v v = 0 := by apply h
  have hw : β w w = 0 := by apply h
  have h1 : β (v+w) (v+w) = (β v) v + (β w) v + (β v) w + (β w) w :=
    calc
    (β (v+w)) (v+w) = (β v) (v+w) + (β w) (v+w) := by rw [LinearMap.BilinForm.add_left]
    _ = (β v) v + (β w) v + (β v) w + (β w) w := by
      rw [LinearMap.BilinForm.add_right v v w, LinearMap.BilinForm.add_right w v w, ← add_assoc]; ring
  have hvw : β (v+w) (v+w) = 0 := by apply h
  rw [hv, hw, hvw, zero_add, add_zero, add_comm] at h1
  have h2: 0 + -(β w) v = (β v) w + (β w) v + -(β w) v := by
    apply (@add_right_cancel_iff _ _ _ (-(β w) v) 0 ((β v) w + (β w) v)).mpr h1
  rw [l, zero_add] at h1
  symm at h1
  exact h1


lemma symm_is_reflexive (β:BilinForm k V) (h:IsSymm β) : IsRefl β := by
  intro v w l
  have h1: (β v) w = (β w) v := by apply h
  rw [l] at h1
  symm at h1
  exact h1

abbrev OrthogSubspacesWeak (β:BilinForm k V) (W₁ W₂ : Submodule k V) : Prop :=
  ∀ x ∈ W₁, ∀ y ∈ W₂, β x y = 0

lemma swap_OrthogSubspacesWeak {β: BilinForm k V} {W₁ W₂: Submodule k V}
  (h: OrthogSubspacesWeak β W₁ W₂) (hr: IsRefl β): OrthogSubspacesWeak β W₂ W₁ := by
  intro x hx y hy
  rw[hr]
  exact h y hy x hx

abbrev OrthogSubspaces (β:BilinForm k V) (W₁ W₂ : Submodule k V) : Prop :=
  OrthogSubspacesWeak β W₁ W₂ ∧ OrthogSubspacesWeak β W₂ W₁

theorem OrthogSubspaces_of_OrthogSubspacesWeak_refl {β: BilinForm k V} {W₁ W₂: Submodule k V}
  (h: OrthogSubspacesWeak β W₁ W₂) (hr: IsRefl β): OrthogSubspaces β W₁ W₂ := by
  constructor
  . exact h
  . exact swap_OrthogSubspacesWeak h hr

theorem OrthogSubspacesWeak_of_orthogonal_complement (β: BilinForm k V) (W: Submodule k V) :
    OrthogSubspacesWeak β W (β.orthogonal W) := by
    unfold OrthogSubspacesWeak
    rintro a ha b hb
    simp at hb
    show β a b =0
    apply hb
    exact ha


-- The mathlib predicate `LinearMap.IsOrthoᵢ` is used to indicate that
-- a collection of vectors is orthogonal with respect to some bilinear
-- form. e.g.

example (β : BilinForm k V) (vect:Fin n → V) : Prop := LinearMap.IsOrthoᵢ β vect

-- the preceding means that `∀ i j : Fin n, i ≠ j → β (vect i) (vect j) = 0`


-- thanks to Sahan for pointing out that the following is avaiable in `mathlib`

-- if we have a function `vect:Fin n → V` that satisfies the predicate
-- `IsOrthoᵢ` and if we know  `∀ i: Fin n, β (vect i) (vect i) ≠ 0` then
-- we can conclude the linear independence of `vect` by using

-- `LinearMap.BilinForm.linearIndependent_of_IsOrthoᵢ`

-- indeed:


example (β : BilinForm k V) (vect:Fin n → V)
  (h₁: LinearMap.IsOrthoᵢ β vect)
  (h₂: ∀ i: Fin n, β (vect i) (vect i) ≠ 0)
  : LinearIndependent k vect := by
  apply LinearMap.linearIndependent_of_isOrthoᵢ h₁
  intro i l
  exact h₂ i l


-- predicate for orthogonality of sets
def OrthogSets  (β:BilinForm k V) (s₁ s₂ : Set V) : Prop :=
  ∀ x₁ ∈ s₁, ∀ x₂ ∈ s₂, β x₁ x₂ = 0

lemma orthog_sets_iff_orthog_subspaces_span (β:BilinForm k V) (s₁ s₂ : Set V) :
  OrthogSets β s₁ s₂ ↔ OrthogSubspacesWeak β (Submodule.span k s₁) (Submodule.span k s₂) := by
  constructor
  . intro h
    unfold OrthogSubspacesWeak
    intro x hx  y hy
    rw[Submodule.mem_span_iff_exists_finset_subset] at hx
    rw[Submodule.mem_span_iff_exists_finset_subset] at hy
    have ⟨fx,tx, hstx, hsuppx, hx⟩ := hx
    have ⟨fy,ty, hsty, hsuppy, hy⟩ := hy
    rw[<- hx, <- hy]
    have (i j: V) (hx: i ∈ tx) (hy : j ∈ ty): β i j =0:= by
      exact h i (hstx hx) j (hsty hy)
    simp_all[-hx, -hy]
  . intro h
    intro x hx y hy
    have hx: x ∈ Submodule.span k s₁ := by exact Submodule.mem_span.mpr fun p a ↦ a hx
    have hy: y ∈ Submodule.span k s₂ := by exact Submodule.mem_span.mpr fun p a ↦ a hy
    simp_all[OrthogSubspacesWeak]


--------------------------------------------------------------------------------
-- non-degenerate forms
-- ====================

@[simp]
theorem mem_orthogonal_iff' (B: BilinForm k V) {W : Submodule k V} {w: V} :
    w ∈ B.orthogonal W ↔ ∀ v ∈ W, B v w=0 := by rfl

example (β: BilinForm k V) :
  β.Nondegenerate ↔ ∀ v:V, (∀ w:V, β v w = 0) → v = 0 := by rfl

def coNondegenerate (β : BilinForm k V) : Prop :=
  ∀ v:V, (∀ w:V, β w v = 0) → v = 0

def NondegenerateOn
  (β : BilinForm k V) (W : Submodule k V) : Prop :=
  (BilinForm.restrict β W).Nondegenerate

lemma coNondegenerate_iff_flip_Nondegenerate (β: BilinForm k V):
  coNondegenerate β ↔ β.flip.Nondegenerate := by
  simp[coNondegenerate, LinearMap.BilinForm.flip, LinearMap.BilinForm.Nondegenerate]

theorem nondeg_conditions (B : BilinForm k V) [FiniteDimensional k V]:
    (B.Nondegenerate) ↔ (coNondegenerate B) := by
    rw[coNondegenerate_iff_flip_Nondegenerate]
    exact LinearMap.BilinForm.nonDegenerateFlip_iff.symm

protected theorem nondeg_via_basis (β: BilinForm k V)
 {ι: Type*} [Fintype ι] [DecidableEq ι] (b: Basis ι k V):
    (β.Nondegenerate)
  ↔ (BilinForm.toMatrix b β).det ≠ 0 := by
  exact BilinForm.nondegenerate_iff_det_ne_zero b

--------------------------------------------------------------------------------
-- direct sums and orthogonal complements
-- ======================================

structure internal_direct_sum (W₁ W₂ : Submodule k V)  where
  zero : W₁ ⊓ W₂ = ⊥
  span : W₁ ⊔ W₂ = ⊤


-- Sahan pointed out that this is the same predicate as `IsCompl`
-- which is defined for bounded a bounded lattice `α`.

-- So we should prove that the notions are the same, so we'll be able
--  use results about `IsCompl`.

-- Sahan: I am not replacing internal_direct_sum with `IsCompl` as it unfolds
--   worse definitionally/when using constructor
--   (though there are useful theorems about it in Mathlib)

lemma direct_sum_iff_iscompl (W₁ W₂ : Submodule k V) :
    BilinearForms.internal_direct_sum W₁ W₂
  ↔ IsCompl W₁ W₂ := by
  constructor
  . intro h
    rw[isCompl_iff]
    constructor
    . rw[disjoint_iff_inf_le]
      rw[h.zero]
    . rw[codisjoint_iff_le_sup]
      rw[h.span]
  . intro h
    have zero: W₁ ⊓ W₂=⊥ := by
      rw[isCompl_iff] at h
      exact disjoint_iff.mp h.left
    have span: W₁ ⊔ W₂=⊤ := by
      rw[isCompl_iff] at h
      exact codisjoint_iff.mp h.right
    exact {zero, span}

/-- Does not gaurantee V ≃ W₁ ⊕ W₂ as bilinear spaces. -/
structure is_orthog_direct_sum_weak (β:BilinForm k V) (W₁ W₂ : Submodule k V) where
  ds : internal_direct_sum W₁ W₂
  orthog : OrthogSubspacesWeak β W₁ W₂

/-- Gaurantees V ≃ W₁ ⊕ W₂ as bilinear spaces. -/
structure is_orthog_direct_sum (β:BilinForm k V) (W₁ W₂ : Submodule k V) where
  ds : internal_direct_sum W₁ W₂
  orthog : OrthogSubspaces β W₁ W₂

lemma is_orthog_direct_sum_of_is_orthog_direct_sum_weak_refl {β: BilinForm k V} {W₁ W₂: Submodule k V}
  (h: is_orthog_direct_sum_weak β W₁ W₂) (hr: IsRefl β): is_orthog_direct_sum β W₁ W₂ := by
  constructor
  . exact h.ds
  . exact OrthogSubspaces_of_OrthogSubspacesWeak_refl h.orthog hr

abbrev orthog_direct_sum_weak (β: BilinForm k V) (W: Submodule k V) :=
  is_orthog_direct_sum_weak β W (orthogonal β W)

abbrev orthog_direct_sum (β: BilinForm k V) (W: Submodule k V) :=
  is_orthog_direct_sum β W (orthogonal β W)

/-- Does not gaurantee W₁ ⊔ W₂ ≃ W₁ ⊕ W₂ as bilinear spaces. -/
structure is_orthog_ind_weak (B: BilinForm k V) (W₁: Submodule k V) (W₂: Submodule k V) where
  ind: W₁ ⊓ W₂ = ⊥
  orthog: OrthogSubspacesWeak B W₁ W₂

/-- Gaurantees W₁ ⊔ W₂ ≃ W₁ ⊕ W₂ as bilinear spaces. -/
structure is_orthog_ind (B: BilinForm k V) (W₁: Submodule k V) (W₂: Submodule k V) where
  ind: W₁ ⊓ W₂ = ⊥
  orthog: OrthogSubspaces B W₁ W₂

lemma is_orthog_ind_of_is_orthog_ind_weak_refl {β: BilinForm k V} {W₁ W₂: Submodule k V}
  (h: is_orthog_ind_weak β W₁ W₂) (hr: IsRefl β): is_orthog_ind β W₁ W₂ := by
  constructor
  . exact h.ind
  . exact OrthogSubspaces_of_OrthogSubspacesWeak_refl h.orthog hr

theorem orthog_inter (β: BilinForm k V) [FiniteDimensional k V] (W: Submodule k V) (wnd: NondegenerateOn β W) :
  W ⊓ (β.orthogonal W) = ⊥ := by
  have wnd : ∀ w:W, (∀ v:W, (β.restrict W) v w = 0) → w = 0 := by
    have := nondeg_conditions (β.restrict W)
    tauto
  suffices W ⊓ β.orthogonal W ≤ ⊥ from ?_
  . exact (Submodule.eq_bot_iff (W ⊓ β.orthogonal W)).mpr this
  intro a ha
  obtain ⟨ha1, ha2⟩ := ha
  have: ∀ b ∈ W, β b a= 0 := by
    intro b hb
    exact ha2 b hb
  show a=0
  simp_all only [BilinForm.restrict_apply, LinearMap.domRestrict_apply, Subtype.forall, Submodule.mk_eq_zero,
    SetLike.mem_coe, implies_true, Submodule.zero_mem, map_zero]

-- Sahan: Better name?
lemma foo_ker_bilin_domRestrict_bot {V : Type*} {K : Type*} [Field K]
   [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (B : BilinForm K V) (W : Submodule K V) (wnd: NondegenerateOn B W) :
    (LinearMap.ker (B.domRestrict W)).map W.subtype = (⊥: Submodule K V) := by
  ext x; constructor
  . rintro ⟨⟨a, ha⟩, h1,h2⟩
    simp at h1
    have h3: (B.restrict W) ⟨a, ha⟩  = 0 := by
      ext y
      simp_all
    have: (⟨a, ha⟩: W) = 0 := by
      apply wnd
      rw[h3]
      simp
    rw[<- h2, this]
    exact rfl
  . rintro ⟨h1, h2⟩
    exact Submodule.zero_mem _

-- Sahan: Better name?
lemma foo_rank_ker_bilin_domRestrict_zero {V : Type*} {K : Type*} [Field K]
   [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (B : BilinForm K V) (W : Submodule K V) (wnd: NondegenerateOn B W) :
    Module.finrank K ((LinearMap.ker (B.domRestrict W)).map W.subtype) = 0 := by
    rw[foo_ker_bilin_domRestrict_bot B W wnd]
    exact finrank_bot K V

theorem finrank_orthogonal_add_total  {V : Type*} {K : Type*} [Field K]
 [AddCommGroup V] [Module K V] [FiniteDimensional K V]
 (B: BilinForm K V) (W : Submodule K V) (wnd : NondegenerateOn B W):
    Module.finrank K W + Module.finrank K (B.orthogonal W) =
      Module.finrank K V := by

  rw[<- add_zero (Module.finrank K V)]
  rw [← foo_rank_ker_bilin_domRestrict_zero B W wnd]

  rw[ ←LinearMap.BilinForm.toLin_restrict_range_dualCoannihilator_eq_orthogonal _ _, Submodule.finrank_map_subtype_eq]
  conv_rhs =>
    rw [← @Subspace.finrank_add_finrank_dualCoannihilator_eq K V _ _ _ _
        (LinearMap.range (B.domRestrict W)),
      add_comm, ← add_assoc, add_comm (Module.finrank K (LinearMap.ker (B.domRestrict W))),
      LinearMap.finrank_range_add_finrank_ker]

theorem isCompl_orthogonal_of_restrict_nondegenerate  {V : Type*} {K : Type*} [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (B: BilinForm K V) (W: Submodule K V)
    (wnd:NondegenerateOn B W )  : IsCompl W (B.orthogonal W) := by
  have : W ⊓ B.orthogonal W = ⊥ := orthog_inter B W wnd

  refine IsCompl.of_eq this (Submodule.eq_top_of_finrank_eq <| (Submodule.finrank_le _).antisymm ?_)
  conv_rhs =>
    rw [← add_zero (Module.finrank K _)]
    rw [← finrank_bot K V]
    rw[← this]
    rw[Submodule.finrank_sup_add_finrank_inf_eq]
    rw[finrank_orthogonal_add_total B W wnd]

theorem internal_direct_sum_of_orthogonal_of_restrict_nondegenerate  {V : Type*} {K : Type*} [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (B: BilinForm K V) (W: Submodule K V)
    (wnd:NondegenerateOn B W )  : internal_direct_sum W (B.orthogonal W) := by
    rw[direct_sum_iff_iscompl]
    exact isCompl_orthogonal_of_restrict_nondegenerate B W wnd

def orthog_decomp_weak (β:BilinForm k V)[FiniteDimensional k V] (W:Submodule k V) (wnd : NondegenerateOn β W):
  orthog_direct_sum_weak β W  where
    ds := internal_direct_sum_of_orthogonal_of_restrict_nondegenerate β W wnd
    orthog := OrthogSubspacesWeak_of_orthogonal_complement β W

-- This could be proved using Mathlib results instead of the machinery here, as this theorem requires Reflexivity
def orthog_decomp (β:BilinForm k V)[FiniteDimensional k V] (W:Submodule k V) (wnd : NondegenerateOn β W) (hr: IsRefl β):
  orthog_direct_sum β W  where
    ds := internal_direct_sum_of_orthogonal_of_restrict_nondegenerate β W wnd
    orthog := OrthogSubspaces_of_OrthogSubspacesWeak_refl (OrthogSubspacesWeak_of_orthogonal_complement β W) hr

end BilinearForms
