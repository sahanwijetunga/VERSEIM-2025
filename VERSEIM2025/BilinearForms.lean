--------------------------------------------------------------------------------
/-
Copyright (c) 2025 Clea Bergsman, Katherine Buesing, George McNinch, Sahan Wijetunga. All rights reserved.

Released under the Apache 2.0 license as described in the file LICENSE.

VERSEIM-2025 REU @ Tufts University 
-/

import Mathlib.Tactic


variable { k V : Type } [Field k] [ AddCommGroup V ]  [Module k V]

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

lemma alt_iff_skew (β:V →ₗ[k] V →ₗ[k] k) 
   [CharP k p] (hn2 : p ≠ 2)
   : Alt β ↔ Skew β := by
   sorry


def OrthogSubspaces (k V:Type) [AddCommGroup V] [Field k] [Module k V] (β:V →ₗ[k] V →ₗ[k] k)
  (W₁ W₂ : Submodule k V) : Prop :=
  ∀ (x:W₁), ∀ (y:W₂), β x y = 0

def fun_is_orthog (β:V →ₗ[k] V →ₗ[k] k) {n:ℕ} (vect : Fin n → V) : Prop :=
  ∀ i j : Fin n, i ≠ j → β (vect i) (vect j) = 0

theorem lin_indep_of_orthog (β:V →ₗ[k] V →ₗ[k] k) (f : Fin n → V) :  LinearIndependent k f := by sorry

