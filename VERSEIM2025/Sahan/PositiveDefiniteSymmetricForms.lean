--------------------------------------------------------------------------------
/-
Copyright (c) 2025 Clea Bergsman, Katherine Buesing, George McNinch, Sahan Wijetunga. All rights reserved.

Released under the Apache 2.0 license as described in the file LICENSE.

VERSEIM-2025 REU VERSEIM-2025 REU @ Tufts University
-/

import Mathlib.Tactic
import VERSEIM2025.Sahan.BilinearForms
import VERSEIM2025.Sahan.Subspaces


-- In this file we consider a vector space over the real numbers ℝ
-- equipped with a positive definite bilinear form

variable { V : Type } [ AddCommGroup V ]  [Module ℝ V]

variable (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ)

def PosDef (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ) : Prop :=
  ∀ x : V, (β x x ≥ 0 ∧( x ≠ 0 → β x x > 0))

-- We are really only interested in the case in which `V` is finite
-- dimensional but initially there is not need to impose that
-- assumption.

-- We propose to prove first a formal proof of "the Gram-Schmidt
-- orthogonalization process".

-- Here is an initial version of the statement probably we should
-- replace `Fin n` by `(ι:Type) [Fintype ι]` but lets do the basic
-- case first.

def Orthog {V : Type} [AddCommGroup V] [ Module ℝ V ] (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
  {n:ℕ} (c:Fin n → V) : Prop := ∀ (i j : Fin n), i ≠ j → β (c i) (c j) = 0

def restrict {X:Type} {m:ℕ} (f:Fin (m+1) → X) : Fin m → X :=
  fun i => f i.castSucc

def extend {X:Type} {m:ℕ} (f:Fin m → X) (x :X) : Fin (m+1) → X :=
  fun i =>
  if h:i ≠ Fin.last m then f (i.castPred h) else x

-- this def needs to produce the orthogonal set

structure orthog_fun (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (n:ℕ) where
   vect : Fin n → V
   is_orthog : fun_is_orthog β vect

def orthog_by_gram_schmidt (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hs : Symm β) {hp : PosDef β} {m:ℕ}
  (b : Fin n → V) (hb : LinearIndependent ℝ b) :
  orthog_fun β n := by sorry

example[AddCommGroup A] (n: ℕ) (f g : Fin n → A) (h: f = g): ∑ i, f i = ∑ i, g i := by
  rw[h]


--------------------------------------------------------------------------------

-- this next result is true in more generality, but let's prove it
-- first in the positive definite setting


theorem lin_indep_of_orthog_subspaces (V : Type) [AddCommGroup V] [Module ℝ V] (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
  (hp:PosDef β) (W₁ W₂ : Submodule ℝ V) (ho: OrthogSubspaces β W₁ W₂)
  (ι₁ ι₂: Type) [Fintype ι₁] [Fintype ι₂]
  (f₁:ι₁ → V) (f₂:ι₂ → V)
  (hi₁:LinearIndependent ℝ f₁) (hi₂:LinearIndependent ℝ f₂)
  (hbw1 : ∀ i, f₁ i ∈ W₁)
   (hbw2 : ∀ i, f₂ i ∈ W₂) :
  LinearIndependent ℝ (disjointUnion_funs f₁ f₂) := by
    apply lin_indep_by_transverse_subspaces
    . exact hi₁
    . exact hi₂
    . show W₁ ⊓ W₂ = ⊥
      suffices W₁ ⊓ W₂ ≤ ⊥ from ?_
      . exact (Submodule.eq_bot_iff (W₁ ⊓ W₂)).mpr this
      intro x ⟨h1, h2⟩
      have: β x x = 0 := by
        unfold OrthogSubspaces at ho
        simp_all
      contrapose! this
      have: x ≠ 0 := by exact this
      have:= (hp x).right this
      exact Ne.symm (ne_of_lt this)
    . intro i
      exact hbw1 i
    . exact fun i ↦ hbw2 i
