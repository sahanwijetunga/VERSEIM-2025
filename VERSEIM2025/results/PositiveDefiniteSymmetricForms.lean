--------------------------------------------------------------------------------
/-
Copyright (c) 2025 Clea Bergsman, Katherine Buesing, George McNinch, Sahan Wijetunga. All rights reserved.

Released under the Apache 2.0 license as described in the file LICENSE.

VERSEIM-2025 REU VERSEIM-2025 REU @ Tufts University 
-/

import Mathlib.Tactic

-- In this file we consider a vector space over the real numbers ℝ
-- equipped with a positive definite bilinear form

variable { V : Type } [ AddCommGroup V ]  [Module ℝ V]

variable (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ)

def PosDef (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ) : Prop :=
  ∀ x : V, β x x ≥ 0 ∧ x ≠ 0 → β x x > 0

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

-- this def produces the (proposed) orthogonal set

def orthog_by_gs {V:Type} [AddCommGroup V] [Module ℝ V] 
  (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hp : PosDef β)
  {m:ℕ}
  (b:Fin (m+1) → V) (hnz : (i:Fin (m+1)) → b i ≠ 0)
  : Fin m → V := match m with 
   | Nat.zero => b
   | Nat.succ m => 
       let initial : Fun m → V := orthog_by_gs (restrict b) (by sorry)
       let last : V := by sorry
       exact extend initial last



