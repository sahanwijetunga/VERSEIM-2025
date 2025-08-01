--------------------------------------------------------------------------------
/-
Copyright (c) 2025 Clea Bergsman, Katherine Buesing, George McNinch, Sahan Wijetunga. All rights reserved.

Released under the Apache 2.0 license as described in the file LICENSE.

VERSEIM-2025 REU @ Tufts University
-/

import Mathlib.Tactic
import Mathlib.Data.Matrix.Rank

open LinearMap (BilinForm)
open LinearMap


variable { k V : Type } [Field k] [ AddCommGroup V ]  [Module k V]

variable (β:V →ₗ[k] V →ₗ[k] k)

def Alt (β:V →ₗ[k] V →ₗ[k] k) : Prop :=
  ∀ v : V, β v v = 0

def Skew (β:V →ₗ[k] V →ₗ[k] k) : Prop :=
  ∀ v w : V, β v w = -β w v

def Symm (β:V →ₗ[k] V →ₗ[k] k) : Prop :=
  ∀ v w : V, β v w = β w v


lemma skew_of_alt (β:V →ₗ[k] V →ₗ[k] k) (ha : Alt β) :
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

--have h1 : (β v) w = -(β w) v := by exact Eq.symm (LinearMap.BilinForm.IsAlt.neg_eq ha w v)
 -- symm at h
  --rw [add_comm] at h
 -- rw [← add_eq_zero_iff_eq_neg'.mp] at h

#check add_assoc
#check add_eq_zero_iff_eq_neg'
#check sub_self
#check congr_arg
#check LinearMap.map_add
#check LinearMap.BilinForm.add_left
#check LinearMap.BilinForm.add_right
#check add_right_cancel_iff
#check sub_eq_add_neg


example (β : V →ₗ[k] V →ₗ[k] k)  (v w x : V) : β (v + w) x = β v x + β w x := by
  have h : β (v + w) = β v + β w := by simp
  rw [h]
  rfl

lemma eq_zero_of_two_mul_eq_zero { k V : Type } [ Field k] [ AddCommGroup V]
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

lemma zero_of_two_mul_eq_zero  { k : Type } [ Field k]
  [CharZero k] (x:k) (h:2*x = 0) : x = 0 := by
  --have nz2_inst : NeZero ↑2 := inferInstance
  have nz2 : (2:k) ≠ 0 := NeZero.ne ↑2
  by_contra x_neq_zero
  have two_mul_ne_zero : ↑2*x ≠ 0 :=
    mul_ne_zero nz2 x_neq_zero
  exact two_mul_ne_zero h

lemma alt_iff_skew (β:V →ₗ[k] V →ₗ[k] k)
   [CharZero k]
   : Alt β ↔ Skew β := by
   constructor
   intro ha
   apply skew_of_alt
   exact ha
   intro hs
   intro v
   have h1 : β v v = -β v v := by apply hs
   have h2 : β v v + β v v = β v v + -β v v := by
     apply (@add_left_cancel_iff _ _ _ (β v v) (β v v) (-β v v)).mpr  h1
   rw [← sub_eq_add_neg, sub_self ((β v) v)] at h2
   rw [← two_mul] at h2
   apply zero_of_two_mul_eq_zero at h2
   exact h2

#check CharZero k


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

-- ===============
-- Reflexive forms
-- ===============

-- Mathlib has a predicate for reflexive forms -- namely
-- `LinearMap.IsRefl`. So it might be useful if we record that our
-- alternating and symmetric forms are reflexive.

#check LinearMap.IsRefl

lemma skew_is_reflexive (β:BilinForm k V) (h:Skew β) : IsRefl β := by
  intro v w l
  rw [h]
  simp
  assumption

lemma alt_is_reflexive (β:BilinForm k V) (h:Alt β) : IsRefl β := by
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

lemma symm_is_reflexive (β:BilinForm k V) (h:Symm β) : IsRefl β := by
  intro v w l
  have h1: (β v) w = (β w) v := by apply h
  rw [l] at h1
  symm at h1
  exact h1

--------------------------------------------------------------------------------
-- non-degenerate forms
-- ====================
noncomputable section

open LinearMap
open LinearMap (BilinForm)

abbrev stdVS  (k:Type) [Field k] (n:ℕ) : Type := (Fin n → k)

abbrev sbv (n:ℕ) : Basis (Fin n) k (stdVS k n) := Pi.basisFun k (Fin n)

def map_of_matrix {m n :ℕ} (M:Matrix (Fin m) (Fin n) k) : stdVS k n →ₗ[k] stdVS k m :=
  Matrix.toLin (sbv n) (sbv m) M

def Nullity (M:Matrix (Fin m) (Fin n) k) : ℕ :=
  let null_space : Submodule k (stdVS k n) :=
    LinearMap.ker M.mulVecLin
  Module.finrank k null_space

lemma mulVecLin_eq_toLin_sbv (M:Matrix (Fin m) (Fin n) k) :
   M.mulVecLin = M.toLin (sbv n) (sbv m) := by
   rfl

lemma rank_eq_linmap_rank  {m n :ℕ} (M:Matrix (Fin m) (Fin n) k) :
   M.rank  = Module.finrank k (LinearMap.range M.mulVecLin)
   := by
   unfold Matrix.rank
   rw [ mulVecLin_eq_toLin_sbv M ]

theorem rank_nullity (M:Matrix (Fin m) (Fin n) k) :
  M.rank + Nullity M = n := by
  unfold Nullity
  rw [ rank_eq_linmap_rank ]
  rw [ LinearMap.finrank_range_add_finrank_ker M.mulVecLin ]
  simp

--def Nondeg (β : BilinForm k V) : Prop :=
  ∀ v:V, (∀ w:V, β v w = 0) → v = 0

--def NondegOn
  (β : BilinForm k V) (W : Subspace k V) : Prop :=
  Nondeg (BilinForm.restrict β W)


theorem nondeg_conditions (β : BilinForm k V) [FiniteDimensional k V] (n : ℕ ) (h: Module.finrank V = n)
  (b : Basis (Fin n) k V):
    (LinearMap.BilinForm.Nondegenerate β)
  ↔ (∀ w:V, (∀ v:V, β v w = 0) → w = 0) := by
  constructor
  intro v w h1
  let M : Matrix (Fin n) (Fin n) k :=
    BilinForm.toMatrix b β
  sorry

theorem nondeg_rank (β : BilinForm k V) [FiniteDimensional k V] (n : ℕ ) (h: Module.rank k V = n)
  (b : Basis (Fin n) k V): (LinearMap.BilinForm.Nondegenerate β) ↔ Matrix.rank (BilinForm.toMatrix b β ) = n := by
  constructor
  -- Nondegenerate β → rank M = n
  intro hn
  have nondeg : β.Nondegenerate := by apply hn
  have nul_zero : LinearMap.ker β = ⊥ := by
    apply LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot.mp; exact nondeg
  let M : Matrix (Fin n) (Fin n) k := BilinForm.toMatrix b β
  have h1 : Module.rank k ↥(range β ) + (Module.rank k (ker β)) = Module.rank k V  :=
      by apply LinearMap.rank_range_add_rank_ker
  have zero : (Module.rank k ↥(ker β)) = 0 := by rw [nul_zero]; simp
  rw [zero, add_zero] at h1
  rw [h] at h1
  simp at h1
  exact h1
  --  rank M = n → Nondegenerate β
  intro hn
  have h1 : Module.rank k ↥(range β ) + (Module.rank k (ker β)) = Module.rank k V  :=
      by apply LinearMap.rank_range_add_rank_ker
  simp at h1
  rw [hn] at h1
  have nul_zero : Module.rank k ↥(ker β) = 0 := by
    apply (add_eq_left _ _ (↑n) (Module.rank k ↥(ker β))).mp at h1
  simp at nul_zero
  apply LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot.mpr
  exact nul_zero

--have det_zero : M.det ≠ 0 := by
    --apply (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp;
    --apply nondeg

#check BilinForm.toMatrix
#check Matrix.rank
#check LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot
#check Matrix.nondegenerate_iff_det_ne_zero
#check LinearMap.BilinForm.nondegenerate_iff_det_ne_zero
#check Matrix.rank_unit --rank of invertible matrix equals full rank
#check LinearMap.ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank
#check LinearMap.BilinForm.nondegenerate_toMatrix_iff
#check LinearMap.BilinForm.nondegenerate_iff_det_ne_zero
#check LinearMap.rank_range_add_rank_ker
#check add_eq_left

theorem nondeg_via_basis (β: BilinForm k V) [FiniteDimensional k V] :
    (LinearMap.BilinForm.Nondegenerate β)
  ↔ (∃ (b:Basis ι k V), (BilinForm.toMatrix b β).det ≠ 0) := by sorry


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
     , zero := by sorry
     }
   orthog := by sorry
