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

-- then we haves

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
  Skew β := by
  intro v w
  suffices β v w + β w v = 0 from ?_
  . exact Eq.symm (LinearMap.BilinForm.IsAlt.neg_eq ha w v)
  calc
    β v w + β w v = β w v + β v w + β v v + β w w := by
      rw[ha v, ha w]
      abel
    _ = β (v+w) (v+w) := by
      simp
      abel
    _ = 0 := ha _


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
   : Alt β ↔ Skew β := by
  constructor
  . apply skew_of_alt
  . intro h
    simp only [Alt, Skew] at *
    intro v
    have: β v v + β v v = 0 := eq_neg_iff_add_eq_zero.mp (h v v)
    have: 2 • β v v = 0 := by rw[(two_nsmul ((β v) v)), this]
    apply eq_zero_of_two_mul_eq_zero_vector k hn2 (β v v) this

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
  intro a b hab
  rw[ skew_of_alt β h]
  simp[hab]


lemma symm_is_reflexive (β:BilinForm k V) (h:Symm β) : IsRefl β := by
  intro a b hab
  rw[h]
  exact hab

def OrthogSubspaces (β:BilinForm k V) (W₁ W₂ : Submodule k V) : Prop :=
  ∀ (x:W₁), ∀ (y:W₂), β x y = 0


theorem OrthogSubspaces_of_orthogonal (β: BilinForm k V) (W: Submodule k V) :
    OrthogSubspaces β W (β.orthogonal W) := by
    unfold OrthogSubspaces
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    simp at hb
    show β a b =0
    apply hb
    exact ha


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
  Nondeg β ↔ β.Nondegenerate := by rfl

lemma co_Nondeg_iff_flip_Nondegenerate (β: BilinForm k V):
  co_Nondeg β ↔ β.flip.Nondegenerate := by
  simp[co_Nondeg, LinearMap.BilinForm.flip, LinearMap.BilinForm.Nondegenerate]

theorem nondeg_conditions (B : BilinForm k V) [FiniteDimensional k V]:
    (Nondeg B) ↔ (co_Nondeg B) := by
    rw[Nondeg_iff_Nondegenerate]
    rw[co_Nondeg_iff_flip_Nondegenerate]
    exact LinearMap.BilinForm.nonDegenerateFlip_iff.symm

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

structure orthog_direct_sum (β:BilinForm k V) (W : Submodule k V) where
  compl : Submodule k V
  ds : internal_direct_sum W compl
  orthog : ∀ w ∈ W, ∀ v ∈ compl, β w v= 0

theorem orthog_inter (β: BilinForm k V) [FiniteDimensional k V] (W: Submodule k V) (wnd: NondegOn β W) :
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
  simp_all only [BilinForm.restrict_apply, domRestrict_apply, Subtype.forall, Submodule.mk_eq_zero,
    SetLike.mem_coe, implies_true, Submodule.zero_mem, map_zero]

-- Sahan: Better name?
lemma foo_ker_bilin_domRestrict_0 {V : Type*} {K : Type*} [Field K]
   [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (B : BilinForm K V) (W : Submodule K V) (wnd: NondegOn B W) :
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
    exact Submodule.zero_mem (Submodule.map W.subtype (ker (domRestrict B W)))

-- Sahan: Better name?
lemma foo_rank_ker_bilin_domRestrict_0 {V : Type*} {K : Type*} [Field K]
   [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (B : BilinForm K V) (W : Submodule K V) (wnd: NondegOn B W) :
    Module.finrank K ((LinearMap.ker (B.domRestrict W)).map W.subtype) = 0 := by
    rw[foo_ker_bilin_domRestrict_0 B W wnd]
    exact finrank_bot K V

-- Sahan: Better name?
lemma foo_inf_orthogonal_top_0{V : Type*} {K : Type*} [Field K]
 [AddCommGroup V] [Module K V] [FiniteDimensional K V]
 (B: BilinForm K V) (W : Submodule K V) (wnd : NondegOn B W) :
 (W ⊓ B.orthogonal ⊤ : Submodule K V)=⊥ := by
    suffices W ⊓ B.orthogonal ⊤ ≤ ⊥ from ?_
    . exact (Submodule.eq_bot_iff (W ⊓ B.orthogonal ⊤)).mpr this

    calc
      W ⊓ B.orthogonal ⊤ ≤W ⊓ B.orthogonal W := by
        suffices (B.orthogonal ⊤) ≤ B.orthogonal W from ?_
        . exact inf_le_inf_left W this
        exact BilinForm.orthogonal_le fun ⦃x⦄ a ↦ trivial
      _ = ⊥ := by rw[orthog_inter B W wnd]

-- Sahan: Better name?
lemma foo_finrank_0{V : Type*} {K : Type*} [Field K]
 [AddCommGroup V] [Module K V] [FiniteDimensional K V]
 (B: BilinForm K V) (W : Submodule K V) (wnd : NondegOn B W) :
 Module.finrank K (W ⊓ B.orthogonal ⊤ : Submodule K V)=(0: ℕ) := by
    rw[foo_inf_orthogonal_top_0 B W wnd]
    exact finrank_bot K V

theorem finrank_orthogonal_add_total  {V : Type*} {K : Type*} [Field K]
 [AddCommGroup V] [Module K V] [FiniteDimensional K V]
 (B: BilinForm K V) (W : Submodule K V) (wnd : NondegOn B W):
    Module.finrank K W + Module.finrank K (B.orthogonal W) =
      Module.finrank K V := by

  rw[<- add_zero (Module.finrank K V)]
  rw [← foo_rank_ker_bilin_domRestrict_0 B W wnd]

  rw[ ←LinearMap.BilinForm.toLin_restrict_range_dualCoannihilator_eq_orthogonal _ _, Submodule.finrank_map_subtype_eq]
  conv_rhs =>
    rw [← @Subspace.finrank_add_finrank_dualCoannihilator_eq K V _ _ _ _
        (LinearMap.range (B.domRestrict W)),
      add_comm, ← add_assoc, add_comm (Module.finrank K (LinearMap.ker (B.domRestrict W))),
      LinearMap.finrank_range_add_finrank_ker]

theorem isCompl_orthogonal_of_restrict_nondegenerate  {V : Type*} {K : Type*} [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (B: BilinForm K V) (W: Submodule K V)
    (wnd:NondegOn B W )  : IsCompl W (B.orthogonal W) := by
  have : W ⊓ B.orthogonal W = ⊥ := orthog_inter B W wnd

  refine IsCompl.of_eq this (Submodule.eq_top_of_finrank_eq <| (Submodule.finrank_le _).antisymm ?_)
  conv_rhs =>
    rw [← add_zero (Module.finrank K _)]
    rw [← finrank_bot K V]
    rw[← this]
    rw[Submodule.finrank_sup_add_finrank_inf_eq]
    rw[finrank_orthogonal_add_total B W wnd]

def orthog_decomp (β:BilinForm k V)[FiniteDimensional k V] (W:Submodule k V) (wnd : NondegOn β W):
  orthog_direct_sum β W where
   compl := β.orthogonal W
   ds := (direct_sum_iff_iscompl _ _).mpr (isCompl_orthogonal_of_restrict_nondegenerate β W wnd)
   orthog := fun w a _ a_1 ↦ a_1 w a


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

-- Sahan: Using `in_span_fin_2_iff_linear_combination` with `foo_fun` should hopefully work.
--  Hopefully there is an easier way to do this but I can't make anything work
-- Sahan: Better name?
lemma foo (v1 v2 v : V)(hv : v ∈ Submodule.span k {v1, v2}) :
  ∃(a b: k), v = a • v1 + b • v2 := by
    have: {v1, v2} = Set.range (foo_fun v1 v2):= by
      ext x
      constructor
      . rintro (h | h)
        . use 0; simp only [foo_fun]; tauto
        . use 1; simp only [foo_fun]; symm; exact h
      . rintro ⟨y, rfl⟩
        match y with
        | ⟨0, _⟩ => simp[foo_fun]
        | ⟨1, _⟩ => simp[foo_fun]
    rw[this] at hv
    have ⟨f, hv⟩ := in_span_fin_2_iff_linear_combination v (foo_fun v1 v2) hv
    use f 0, f 1
    rw[hv]
    exact Fin.sum_univ_two fun i ↦ f i • foo_fun v1 v2 i



theorem hyp2_nondeg_refl (β:BilinForm k V)
  (brefl : IsRefl β) {e f : V} (h2: hyp_pair β e f) :
  NondegOn β (hypsubspace β h2) := by
    rintro ⟨v, hv⟩  h
    have: ∃(a b: k), v = a • e + b • f := by
      unfold hypsubspace at hv
      exact foo e f v hv
    have ⟨a,b,hab⟩ := this
    have hve: β v e = 0 := by
      have he: e ∈ hypsubspace β h2 := by
        simp[hypsubspace]
        suffices e ∈ ({e,f} : Set V)from ?_
        . exact Submodule.mem_span_of_mem this
        exact Set.mem_insert e {f}
      apply h ⟨e, he⟩

    have hvf: β v f = 0 := by
      have hf: f ∈ hypsubspace β h2 := by
        simp[hypsubspace]
        suffices f ∈ ({e,f} : Set V)from ?_
        . exact Submodule.mem_span_of_mem this
        exact Set.mem_insert_of_mem e rfl
      apply h ⟨f, hf⟩

    have hveb: β e v = b := by
      calc
        β e v = β e (a• e + b • f) := by rw[hab]
        _ = a * β e e + b * β e f := by simp
        _ = a * 0 + b * 1 := by
          unfold hyp_pair at h2
          have: β e e = 0 := by
            exact h2.left
          have: β e f= 1 := by
            exact h2.right.right
          simp[*]
        _ =  b := by simp
    have hvfa: β v f = a:= by
        calc
        β v f = β (a• e + b • f) f := by rw[hab]
        _ = a * β e f + b * β f f := by simp
        _ = a * 1 + b * 0 := by
          unfold hyp_pair at h2
          have: β e f = 1 := by
            exact h2.right.right
          have: β f f = 0 := by
            exact h2.right.left
          simp[*]
        _ = a := by simp
    have hva: a=0 :=
      calc
        a= β v f := hvfa.symm
        _ = 0 := hvf
    have hvb: b=0 := by
      have hve': β e v = 0 := brefl v e hve
      calc
        b = β e v:= hveb.symm
        _ = 0 := hve'

    simp[hab,hva,hvb]

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
    have: ∃ f, B e f ≠ 0 := by
      contrapose! enz
      exact hn e enz
    have ⟨f, hf⟩ := this
    let a := B e f
    use a⁻¹ • f
    calc
      (B e) (a⁻¹ • f) = a⁻¹ * (B e f) := by simp only [map_smul, smul_eq_mul]
      _ = a⁻¹ * a := rfl
      _ = 1 := inv_mul_cancel₀ hf

theorem hyp_pair_exists_symm {β:BilinForm k V} (bsymm : Symm β) (hn: Nondeg β) (enz : e ≠ 0)
   (eiso : β e e  = 0) [CharP k p] (hn2 : p ≠ 2):
   ∃ f, hyp_pair β e f := by
    have ⟨v, hv⟩ := exists_nice_f enz hn
    let c := - 2⁻¹ * β v v
    let v' := v+c • e
    use v'
    constructor
    . exact eiso
    constructor
    . unfold v' c
      have : β v e = 1 := by
        rw[bsymm]
        exact hv
      have: (2: k) ≠ 0 := by
        apply Ring.two_ne_zero
        rw [ ringChar.eq k p ]
        exact hn2
      field_simp[*]
      ring
    . unfold v' c
      simp_all


theorem hyp_pair_exists_alt {β:BilinForm k V} (balt : Alt β) (hn: Nondeg β) (enz : e ≠ 0) :
   ∃ f, hyp_pair β e f := by
  have ⟨v, hv⟩ := exists_nice_f enz hn
  use v
  constructor; . exact balt e
  constructor
  . exact balt v
  . exact hv
