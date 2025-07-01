--------------------------------------------------------------------------------
/-
Copyright (c) 2025 Clea Bergsman, Katherine Buesing, George McNinch, Sahan Wijetunga. All rights reserved.

Released under the Apache 2.0 license as described in the file LICENSE.

VERSEIM-2025 REU @ Tufts University
-/

import Mathlib.Tactic


variable { k V : Type } [Field k] [ AddCommGroup V ]  [Module k V]


variable { ι : Type } [Fintype ι] [DecidableEq ι]

def Alt (β:V →ₗ[k] V →ₗ[k] k) : Prop :=
  ∀ v : V, β v v = 0

def Skew (β:V →ₗ[k] V →ₗ[k] k) : Prop :=
  ∀ v w : V, β v w = - β w v

def Symm (β:V →ₗ[k] V →ₗ[k] k) : Prop :=
  ∀ v w : V, β v w = β w v

lemma skew_of_alt (β:V →ₗ[k] V →ₗ[k] k) (ha : Alt β) :
  Skew β := by
  intro v w
  suffices β v w + β w v = 0 from ?_
  . exact Eq.symm (LinearMap.BilinForm.IsAlt.neg_eq ha w v)
  calc
    β v w + β w v = β v w+ β w v + β v v + β w w := by
      rw[ha v, ha w]
      abel
    _ = β (v+w) (v+w) := by
      simp
      abel
    _ = 0 := ha _

-- the next lemma says that for a vector space over a field k of
-- characteristic different from 2, for v in V the equation `2v=0`
-- implies that `v=0`.


lemma eq_zero_of_two_mul_eq_zero  { k : Type } [ Field k]
  [CharZero k] (x:k) (h:2*x = 0) : x = 0 := by
  --have nz2_inst : NeZero ↑2 := inferInstance
  have nz2 : (2:k) ≠ 0 := NeZero.ne ↑2
  by_contra x_neq_zero
  have two_mul_ne_zero : ↑2*x ≠ 0 :=
    mul_ne_zero nz2 x_neq_zero
  exact two_mul_ne_zero h

lemma eq_zero_of_two_mul_eq_zero' { k : Type } [ Field k]
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

lemma eq_zero_of_two_mul_eq_zero_vector (k: Type) { V : Type }
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
    simp[Alt, Skew] at *
    intro v
    have: β v v + β v v = 0 := eq_neg_iff_add_eq_zero.mp (h v v)
    have: 2 • β v v = 0 := by rw[(two_nsmul ((β v) v)), this]
    apply eq_zero_of_two_mul_eq_zero_vector k hn2 (β v v) this

-- REMARK: we are really only interested in the case of forms which
-- are either alternating or symmetric.  We are going to formulate a
-- number of predicates on forms which in the general case (of a form
-- which is neither alternating nor symmetric) should have a more
-- complicated definition.


def OrthogSubspaces (β:V →ₗ[k] V →ₗ[k] k) (W₁ W₂ : Submodule k V) : Prop :=
  ∀ (x:W₁), ∀ (y:W₂), β x y = 0

def fun_is_orthog (β:V →ₗ[k] V →ₗ[k] k) {n:ℕ} (vect : Fin n → V) : Prop :=
  ∀ i j : Fin n, i ≠ j → β (vect i) (vect j) = 0



lemma linear_independence_equiv_condition_fin {V:Type} [AddCommGroup V] [Module ℝ V] {n: ℕ} (b: Fin n → V)
(h: ∀(l: Fin n → ℝ), ∑ i, (l i) • (b i)=0 → l=0): LinearIndependent ℝ b := by
    exact Fintype.linearIndependent_iff.mpr fun g a ↦ congrFun (h g a)

/- Sahan:

  LinearMap.BilinForm.linearIndependent_of_iIsOrtho
  would prove the below theorem if we have the hypothesis
     B (f i) (f i) ≠ 0 for all i: Fin n

-/
theorem lin_indep_of_orthog (β:V →ₗ[k] V →ₗ[k] k) (f : Fin n → V)
   (ho: fun_is_orthog β f):  LinearIndependent k f := by
  sorry

-- predicate for orthogonality of sets
def OrthogSets  (β:V →ₗ[k] V →ₗ[k] k) (s₁ s₂ : Set V) : Prop :=
  ∀ x₁ ∈ s₁, ∀ x₂ ∈ s₂, β x₁ x₂ = 0


lemma orthog_sets_iff_orthog_subspaces (β:V →ₗ[k] V →ₗ[k] k) (s₁ s₂ : Set V) :
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
    have hx: x ∈ Submodule.span k s₁ := Submodule.mem_span.mpr fun p a ↦ a hx
    have hy: y ∈ Submodule.span k s₂ := Submodule.mem_span.mpr fun p a ↦ a hy
    simp_all[OrthogSubspaces]


--------------------------------------------------------------------------------
-- non-degenerate forms
-- ====================

open LinearMap
open LinearMap (BilinForm)


def Nondeg (β : BilinForm k V) : Prop :=
  ∀ v:V, (∀ w:V, β v w = 0) → v = 0

def NondegOn
  (β : BilinForm k V) (W : Subspace k V) : Prop :=
  Nondeg (BilinForm.restrict β W)



theorem nondeg_conditions  (β : BilinForm k V) : List.TFAE [ Nondeg β                                -- left-nondegenate
               , ∀ w:V, (∀ v:V, β v w = 0) → w = 0                          -- right-nondegenerate
               , ∃ (b:Basis ι k V), (BilinForm.toMatrix b β).det ≠ 0
               ] := by sorry

/- Sahan: Using nondeg_conditions was painful so I separate this result out
Note: To prove this we would need to add (at least) a hypothesis that
V is finite dimensional, and also add it to future things relying on this
(for those that don't include ι in the statement of the theorem)
-/

theorem nondeg_conditions' (β : BilinForm k V) :
  (Nondeg β) ↔ (∀ w:V, (∀ v:V, β v w = 0) → w = 0) := by sorry


example
  (β: BilinForm k V) (W: Submodule k V): List.TFAE [ Nondeg (β.restrict W)
               , ∀ w:W, (∀ v:W, β v w = 0) → w = 0
               , ∃ (b:Basis ι k W), (BilinForm.toMatrix b (β.restrict W)).det ≠ 0
               ]  := nondeg_conditions (β.restrict W)

--------------------------------------------------------------------------------
-- direct sums and orthogonal complements
-- ======================================


/- Sahan:


IsCompl in Mathlib formalizes similar thing to internal_direct_sum

`LinearMap.BilinForm.orthogonal` formalizes the (left) orthogonal complement

The only relevant theorem I could find is
  `BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal`
  which requires the form to be reflexive (and v.s. finite dimensional)

-/

structure internal_direct_sum (W₁ W₂ : Submodule k V) where
  span : ⊤ = W₁ ⊔ W₂
  zero : ⊥ = W₁ ⊓ W₂

structure orthog_direct_sum (β:BilinForm k V) (W : Submodule k V) where
  compl : Submodule k V
  ds : internal_direct_sum W compl
  orthog : ∀ v₁ ∈ W, ∀ v₂ ∈ compl, β v₁ v₂ = 0

def OrthogCompl {k V:Type} [AddCommGroup V] [Field k] [Module k V] (S : Set V)
    (β:BilinForm k V)
    : Subspace k V where
  carrier := { v | ∀ (x:S), β x v = 0 }
  add_mem' := by
    intro a b ha hb
    intro s
    simp_all only [Subtype.forall, Set.mem_setOf_eq, map_add, add_apply, Subtype.coe_prop, add_zero]
  zero_mem' := by
    intro s
    simp
  smul_mem' := by
    intro c a ha
    simp_all only [Subtype.forall, Set.mem_setOf_eq, map_smul, smul_apply, smul_eq_mul, mul_zero,
      implies_true]

-- Sahan: Do we need some finite dimensional requirement?
def orthog_decomp (β:BilinForm k V) (W:Submodule k V) (wnd : NondegOn β W):
  orthog_direct_sum β W where
   compl := OrthogCompl W β
   ds :=
     { span := by sorry
     , zero := by
        have wnd' : ∀ w:W, (∀ v:W, (β.restrict W) v w = 0) → w = 0 := by
          have:= nondeg_conditions' (β.restrict W)
          tauto
        symm
        suffices W ⊓ OrthogCompl (↑W) β ≤ ⊥ from ?_
        . exact (Submodule.eq_bot_iff (W ⊓ OrthogCompl (↑W) β)).mpr this
        intro a ha
        obtain ⟨ha1, ha2⟩ := ha
        -- Sahan: This have statement is very slow to compile,
        --  maybe prove more explicitly without simp
        have: ∀ b ∈ W, β b a = 0 := by
          simp_all only [BilinForm.restrict_apply, domRestrict_apply, Subtype.forall,
            Submodule.mk_eq_zero, SetLike.mem_coe, OrthogCompl, SetLike.coe_sort_coe,
            SetLike.coe_mem, Submodule.coe_set_mk, AddSubmonoid.coe_set_mk,
            AddSubsemigroup.coe_set_mk, Set.mem_setOf_eq, implies_true, Submodule.zero_mem,
            map_zero, zero_apply]
        show a=0
        simp_all only [BilinForm.restrict_apply, domRestrict_apply, Subtype.forall,
          Submodule.mk_eq_zero, SetLike.mem_coe, implies_true, Submodule.zero_mem, map_zero]
    }
   orthog := by
    intro a ha b hb
    simp_all[OrthogCompl]


--------------------------------------------------------------------------------
-- hyperbolic subspaces
-- ====================


def hyp_pair (β:BilinForm k V) (e f : V) : Prop :=
        β e e = 0  ∧  β f f = 0  ∧  β e f = 1

def hypsubspace (β:BilinForm k V) {e f : V} (_:hyp_pair β e f) : Subspace k V :=
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
    sorry

-- Sahan: proof has some apparent redundancies but I don't see how to simplify
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

def hyp2_decomp_symm (β:BilinForm k V) (bsymm : Symm β) (e f : V) (h2:hyp_pair β e f)
  : orthog_direct_sum β (hypsubspace β h2) :=
  orthog_decomp β (hypsubspace β h2) (hyp2_nondeg_symm  β bsymm h2)

def hyp2_decomp_alt (β:BilinForm k V) (balt : Alt β) (e f : V) (h2:hyp_pair β e f)
  : orthog_direct_sum β (hypsubspace β h2) :=
  orthog_decomp β (hypsubspace β h2) (hyp2_nondeg_alt  β balt h2)


-- finally, we need

theorem hyp_pair_exists_symm (β:BilinForm k V) (bsymm : Symm β) (e:V) (enz : e ≠ 0) (eiso : β e e  = 0)
  (hnl : ⊤ ≠ Submodule.span k {e}):
   ∃ f, hyp_pair β e f := by sorry

theorem hyp_pair_exists_alt (β:BilinForm k V) (bsymm : Symm β) (e:V) (enz : e ≠ 0)
  (hnl : ⊤ ≠ Submodule.span k {e}):
   ∃ f, hyp_pair β e f := by sorry
