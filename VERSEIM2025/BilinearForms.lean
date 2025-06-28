--------------------------------------------------------------------------------
/-
Copyright (c) 2025 Clea Bergsman, Katherine Buesing, George McNinch, Sahan Wijetunga. All rights reserved.

Released under the Apache 2.0 license as described in the file LICENSE.

VERSEIM-2025 REU @ Tufts University
-/

import Mathlib.Tactic


variable { k V : Type } [Field k] [ AddCommGroup V ]  [Module k V]


variable { ι : Type } [Fintype ι] [DecidableEq ι]

variable { b : Basis ι k V }

variable (β:V →ₗ[k] V →ₗ[k] k)

def Alt (β:V →ₗ[k] V →ₗ[k] k) : Prop :=
  ∀ v : V, β v v = 0

def Skew (β:V →ₗ[k] V →ₗ[k] k) : Prop :=
  ∀ v w : V, β v w = β w v

def Symm (β:V →ₗ[k] V →ₗ[k] k) : Prop :=
  ∀ v w : V, β v w = β w v

lemma skew_of_alt (β:V →ₗ[k] V →ₗ[k] k) (ha : Alt β) :
  Skew β := by
  sorry

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

lemma eq_zero_of_two_mul_eq_zero_vector { k V : Type }
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
   sorry

-- REMARK: we are really only interested in the case of forms which
-- are either alternating or symmetric.  We are going to formulate a
-- number of predicates on forms which in the general case (of a form
-- which is neither alternating nor symmetric) should have a more
-- complicated definition.


def OrthogSubspaces (β:V →ₗ[k] V →ₗ[k] k) (W₁ W₂ : Submodule k V) : Prop :=
  ∀ (x:W₁), ∀ (y:W₂), β x y = 0

def fun_is_orthog (β:V →ₗ[k] V →ₗ[k] k) {n:ℕ} (vect : Fin n → V) : Prop :=
  ∀ i j : Fin n, i ≠ j → β (vect i) (vect j) = 0

theorem lin_indep_of_orthog (β:V →ₗ[k] V →ₗ[k] k) (f : Fin n → V) :  LinearIndependent k f := by sorry


-- predicate for orthogonality of sets
def OrthogSets  (β:V →ₗ[k] V →ₗ[k] k) (s₁ s₂ : Set V) : Prop :=
  ∀ x₁ ∈ s₁, ∀ x₂ ∈ s₂, β x₁ x₂ = 0


lemma orthog_sets_iff_orthog_subspaces (β:V →ₗ[k] V →ₗ[k] k) (s₁ s₂ : Set V) :
  OrthogSets β s₁ s₂ ↔ OrthogSubspaces β (Submodule.span k s₁) (Submodule.span k s₂) := by sorry

--------------------------------------------------------------------------------
-- non-degenerate forms
-- ====================

open LinearMap 
open LinearMap (BilinForm)


def Nondeg (β : BilinForm k V) : Prop := 
  ∀ v:V, ∀ w:V, β v w = 0 → v = 0

def NondegOn
  (β : BilinForm k V) (W : Subspace k V) : Prop := 
  Nondeg (BilinForm.restrict β W)



theorem nondeg_conditions  (β : BilinForm k V) 
  : List.TFAE [ Nondeg β                                                 -- left-nondegenate
               , ∀ w:V, ∀ v:V, β v w = 0 → w = 0                          -- right-nondegenerate
               , ∃ (b:Basis ι k V), (BilinForm.toMatrix b β).det ≠ 0
               ] := by sorry


--------------------------------------------------------------------------------
-- direct sums and orthogonal complements
-- ======================================

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
  carrier := { v | ∀ (x:S), β v x = 0 }
  add_mem' := by sorry
  zero_mem' := by sorry
  smul_mem' := by sorry

def orthog_decomp (β:BilinForm k V) (W:Submodule k V) (wnd : NondegOn β W):
  orthog_direct_sum β W where
   compl := OrthogCompl W β
   ds := 
     { span := by sorry
     , zero := by sorry
     }
   orthog := by sorry

--------------------------------------------------------------------------------
-- hyperbolic subspaces
-- ====================

def hyp_pair (β:BilinForm k V) (e f : V) : Prop :=
        β e e = 0  ∧  β f f = 0  ∧  β e f = 1

def hypsubspace (β:BilinForm k V) {e f : V} (h:hyp_pair β e f) : Subspace k V := 
  Submodule.span k {e,f}

theorem hyp2_nondeg_symm (β:BilinForm k V) 
  (bsymm : Symm β) {e f : V} (h2: hyp_pair β e f) :
  NondegOn β (hypsubspace β h2)  := by sorry

theorem hyp2_nondeg_alt (β:BilinForm k V) 
  (balt : Alt β) {e f : V} (h2: hyp_pair β e f) :
  NondegOn β (hypsubspace β h2)  := by sorry


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
  
