--------------------------------------------------------------------------------
/-
Copyright (c) 2025 Clea Bergsman, Katherine Buesing, George McNinch, Sahan Wijetunga. All rights reserved.

Released under the Apache 2.0 license as described in the file LICENSE.

VERSEIM-2025 REU @ Tufts University
-/

import Mathlib.Tactic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal


variable { k V : Type* } [Field k] [ AddCommGroup V ]  [Module k V]

-- let's use the MathLib notions for Bilinear forms

open LinearMap (BilinForm)
open LinearMap

-- then we have

example : (V →ₗ[k] V →ₗ[k] k) = (BilinForm k V) := rfl

def Alt (β:BilinForm k V) : Prop :=
  ∀ v : V, β v v = 0

def Skew (β:BilinForm k V) : Prop :=
  ∀ v w : V, β v w = - β w v

def Symm (β:BilinForm k V) : Prop :=
  ∀ v w : V, β v w = β w v

-- a bilinear form is said to be reflexive if `∀ x y, β x y = 0 → β y
-- x = 0`.


lemma skew_of_alt (β:BilinForm k V) (ha : Alt β) :
  Skew β := by sorry


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


lemma alt_iff_skew (β:V →ₗ[k] V →ₗ[k] k)
   [CharP k p] (hn2 : p ≠ 2)
   : Alt β ↔ Skew β := by sorry

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

lemma alt_is_reflexive (β:BilinForm k V) (h:Alt β) : IsRefl β := by
  sorry


lemma symm_is_reflexive (β:BilinForm k V) (h:Symm β) : IsRefl β := by
  sorry

def OrthogSubspaces (β:BilinForm k V) (W₁ W₂ : Submodule k V) : Prop :=
  ∀ (x:W₁), ∀ (y:W₂), β x y = 0


theorem OrthogSubspaces_of_orthogonal (β: BilinForm k V) (W: Submodule k V) :
    OrthogSubspaces β W (β.orthogonal W) := by
    sorry


-- The mathlib predicate `LinearMap.IsOrthoᵢ` is used to indicate that
-- a collection of vectors is orthogonal with respect to some bilinear
-- form. e.g.

example (β : BilinForm k V) (vect:Fin n → V) : Prop := IsOrthoᵢ β vect

-- the preceding means that `∀ i j : Fin n, i ≠ j → β (vect i) (vect j) = 0`


-- thanks to Sahan for pointing out that the following is avaiable in `mathlib`

-- if we have a function `vect:Fin n → V` that satisfies the predicate
-- `IsOrthoᵢ` and if we know  `∀ i: Fin n, β (vect i) (vect i) ≠ 0` then
-- we can conclude the linear independence of `vect` by using

-- `LinearMap.BilinForm.linearIndependent_of_IsOrthoᵢ`

-- indeed:


example (β : BilinForm k V) (vect:Fin n → V)
  (h₁: IsOrthoᵢ β vect)
  (h₂: ∀ i: Fin n, β (vect i) (vect i) ≠ 0)
  : LinearIndependent k vect := by
  apply linearIndependent_of_isOrthoᵢ h₁
  intro i l
  exact h₂ i l


-- predicate for orthogonality of sets
def OrthogSets  (β:BilinForm k V) (s₁ s₂ : Set V) : Prop :=
  ∀ x₁ ∈ s₁, ∀ x₂ ∈ s₂, β x₁ x₂ = 0


lemma orthog_sets_iff_orthog_subspaces (β:BilinForm k V) (s₁ s₂ : Set V) :
  OrthogSets β s₁ s₂ ↔ OrthogSubspaces β (Submodule.span k s₁) (Submodule.span k s₂) := by
  constructor
  . intro h
    unfold OrthogSubspaces
    intro ⟨x, hx⟩  ⟨y, hy⟩
    rw[Submodule.mem_span_iff_exists_finset_subset] at hx
    rw[Submodule.mem_span_iff_exists_finset_subset] at hy
    simp
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
    simp_all[OrthogSubspaces]


--------------------------------------------------------------------------------
-- non-degenerate forms
-- ====================

open LinearMap
open LinearMap (BilinForm)


def Nondeg (β : BilinForm k V) : Prop :=
  ∀ v:V, (∀ w:V, β v w = 0) → v = 0

def co_Nondeg (β : BilinForm k V) : Prop :=
  ∀ v:V, (∀ w:V, β w v = 0) → v = 0

def NondegOn
  (β : BilinForm k V) (W : Submodule k V) : Prop :=
  Nondeg (BilinForm.restrict β W)

lemma Nondeg_iff_Nondegenerate (β: BilinForm k V):
  Nondeg β ↔ β.Nondegenerate := by
    sorry

lemma co_Nondeg_iff_flip_Nondegenerate (β: BilinForm k V):
  co_Nondeg β ↔ β.flip.Nondegenerate := by
  sorry

theorem nondeg_conditions (B : BilinForm k V) [FiniteDimensional k V]:
    (Nondeg B) ↔ (co_Nondeg B) := by
    sorry

theorem nondeg_via_basis (β: BilinForm k V)
 {ι: Type*} [Fintype ι] [DecidableEq ι] (b: Basis ι k V):
    (Nondeg β)
  ↔ (BilinForm.toMatrix b β).det ≠ 0 := by
  rw[Nondeg_iff_Nondegenerate]
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

lemma direct_sum_iff_iscompl (W₁ W₂ : Submodule k V) :
    internal_direct_sum W₁ W₂
  ↔ IsCompl W₁ W₂ := by sorry

structure orthog_direct_sum (β:BilinForm k V) (W : Submodule k V) where
  compl : Submodule k V
  ds : internal_direct_sum W compl
  orthog : ∀ w ∈ W, ∀ v ∈ compl, β w v= 0

theorem orthog_inter (β: BilinForm k V) [FiniteDimensional k V] (W: Submodule k V) (wnd: NondegOn β W) :
  W ⊓ (β.orthogonal W) = ⊥ := by
  sorry


namespace Hidden
/- Sahan:
This namespace is purely to prove isCompl_orthogonal_of_restrict_nondegenerate.
I wanted to avoid access to
    `finrank_add_finrank_orthogonal`, `toLin_restrict_ker_eq_inf_orthogonal`,
which are proven in Mathlib using the condtion
    `LinearMap.IsRefl`
instead of a nondegeneracy condition.
- Note: (Hidden) finrank_add_finrank_orthogonal could be useful elsewhere as well.

The proof of `finrank_add_finrank_orthogonal` and `isCompl_orthogonal_of_restrict_nondegenerate`
are essentially taken from Mathlib, with minor modifications to accomodate
different conditions

`toLin_restrict_ker_eq_inf_orthogonal` is somewhat degenerate assuming
    `NondegOn B W`
as both sides are just `0` then.
-/


open Module Submodule

protected lemma toLin_restrict_ker_eq_inf_orthogonal'  {V : Type*} {K : Type*} [Field K]
   [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (B : BilinForm K V) (W : Submodule K V) (wnd: NondegOn B W) :
    (LinearMap.ker (B.domRestrict W)).map W.subtype = (W ⊓ B.orthogonal ⊤ : Submodule K V) := by
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
    exact (Quotient.mk_eq_zero (W ⊓ B.orthogonal ⊤)).mp rfl
  . rintro ⟨h1, h2⟩
    have h3: x ∈ B.orthogonal W := by
      intro y hy
      show B y x = 0
      exact h2 y trivial
    have h4: x ∈ W ⊓ B.orthogonal W := mem_inf.mpr ⟨h1, h3⟩
    have h5: x=0 := by
      rw[orthog_inter B W wnd] at h4
      exact h4
    rw[h5]
    exact Submodule.zero_mem (map W.subtype (ker (domRestrict B W)))


protected lemma finrank_add_finrank_orthogonal'  {V : Type*} {K : Type*} [Field K]
 [AddCommGroup V] [Module K V] [FiniteDimensional K V]
 (B: BilinForm K V) (W : Submodule K V) (wnd : NondegOn B W):
    finrank K W + finrank K (B.orthogonal W) =
      finrank K V + finrank K (W ⊓ B.orthogonal ⊤ : Submodule K V) := by
  rw [← Hidden.toLin_restrict_ker_eq_inf_orthogonal' B W wnd]
  rw[ ←LinearMap.BilinForm.toLin_restrict_range_dualCoannihilator_eq_orthogonal _ _, finrank_map_subtype_eq]
  conv_rhs =>
    rw [← @Subspace.finrank_add_finrank_dualCoannihilator_eq K V _ _ _ _
        (LinearMap.range (B.domRestrict W)),
      add_comm, ← add_assoc, add_comm (finrank K (LinearMap.ker (B.domRestrict W))),
      LinearMap.finrank_range_add_finrank_ker]

theorem isCompl_orthogonal_of_restrict_nondegenerate  {V : Type*} {K : Type*} [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (B: BilinForm K V) (W: Submodule K V)
    (wnd:NondegOn B W )  : IsCompl W (B.orthogonal W) := by
  have : W ⊓ B.orthogonal W = ⊥ := orthog_inter B W wnd

  refine IsCompl.of_eq this (eq_top_of_finrank_eq <| (finrank_le _).antisymm ?_)
  conv_rhs => rw [← add_zero (finrank K _)]
  rw [← finrank_bot K V]
  rw[← this]
  rw[finrank_sup_add_finrank_inf_eq]
  rw[Hidden.finrank_add_finrank_orthogonal' B W wnd]
  exact le_self_add

end Hidden

def orthog_decomp (β:BilinForm k V)[FiniteDimensional k V] (W:Submodule k V) (wnd : NondegOn β W):
  orthog_direct_sum β W where
    compl := β.orthogonal W
    ds := (direct_sum_iff_iscompl _ _).mpr (Hidden.isCompl_orthogonal_of_restrict_nondegenerate β W wnd)
    orthog := by
      sorry


--------------------------------------------------------------------------------
-- hyperbolic subspaces
-- ====================


def hyp_pair (β:BilinForm k V) (e f : V) : Prop :=
        β e e = 0  ∧  β f f = 0  ∧  β e f = 1

def hypsubspace (β:BilinForm k V) {e f : V} (_:hyp_pair β e f) : Submodule k V :=
  Submodule.span k {e,f}

-- Sahan: Simplify name?
lemma in_span_fin_n_iff_linear_combination (n: ℕ) (v: V) (vect: Fin n → V) (hv : v ∈ Submodule.span k (Set.range vect)) :
  ∃(f: Fin n → k), v = ∑ i, f i • (vect i) := by
    rw[Submodule.mem_span_range_iff_exists_fun] at hv
    have ⟨c, hc⟩ := hv
    use c
    symm
    exact hc

-- Sahan: Simplify name?
lemma in_span_fin_2_iff_linear_combination (v: V) (vect: Fin 2 → V) (hv : v ∈ Submodule.span k (Set.range vect)) :
  ∃(f: Fin 2 → k), v = ∑ i, f i • (vect i) := by
    exact in_span_fin_n_iff_linear_combination (2: ℕ) (v: V) (vect: Fin 2 → V) hv

-- Sahan: Better name?
def foo_fun (e f : V) : Fin 2 → V
| ⟨0, _⟩ => e
| ⟨1, _⟩ => f

-- Sahan: Using `in_span_fin_2_iff_linear_combination` with `foo_fun` should work.
-- Sahan: Better name?
lemma foo (v1 v2 v : V)(hv : v ∈ Submodule.span k {v1, v2}) :
  ∃(a b: k), v = a • v1 + b • v2 := by
    sorry

theorem hyp2_nondeg_refl (β:BilinForm k V)
  (brefl : IsRefl β) {e f : V} (h2: hyp_pair β e f) :
  NondegOn β (hypsubspace β h2) := by
    sorry

theorem hyp2_nondeg_symm (β:BilinForm k V)
  (bsymm : Symm β) {e f : V} (h2: hyp_pair β e f) :
  NondegOn β (hypsubspace β h2)  := by
  have brefl: IsRefl β := IsSymm.isRefl bsymm
  exact hyp2_nondeg_refl β brefl h2

theorem hyp2_nondeg_alt (β:BilinForm k V)
  (balt : Alt β) {e f : V} (h2: hyp_pair β e f) :
  NondegOn β (hypsubspace β h2)  := by
  have brefl: IsRefl β := IsAlt.isRefl balt
  exact hyp2_nondeg_refl β brefl h2


-- using `orthog_decomp` above, we get

def hyp2_decomp_symm (β:BilinForm k V) [FiniteDimensional k V] (bsymm : Symm β) (e f : V) (h2:hyp_pair β e f)
  : orthog_direct_sum β (hypsubspace β h2) :=
  orthog_decomp β (hypsubspace β h2) (hyp2_nondeg_symm  β bsymm h2)

def hyp2_decomp_alt (β:BilinForm k V) [FiniteDimensional k V] (balt : Alt β) (e f : V) (h2:hyp_pair β e f)
  : orthog_direct_sum β (hypsubspace β h2) :=
  orthog_decomp β (hypsubspace β h2) (hyp2_nondeg_alt  β balt h2)


-- finally, we need

-- Sahan: Better name?
lemma exists_nice_f {B: BilinForm k V} (enz: e ≠ 0)
  (hn: Nondeg B): ∃f, B e f =1 := by
    sorry

theorem hyp_pair_exists_symm {β:BilinForm k V} (bsymm : Symm β) (hn: Nondeg β) (enz : e ≠ 0)
  (eiso : β e e  = 0) [CharP k p] (hn2 : p ≠ 2):
  ∃ f, hyp_pair β e f := by
    sorry


theorem hyp_pair_exists_alt {β:BilinForm k V} (balt : Alt β) (hn: Nondeg β) (enz : e ≠ 0) :
  ∃ f, hyp_pair β e f := by
    sorry
