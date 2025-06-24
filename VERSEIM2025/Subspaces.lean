
--------------------------------------------------------------------------------
/-
Copyright (c) 2025 Clea Bergsman, Katherine Buesing, George McNinch, Sahan Wijetunga. All rights reserved.

Released under the Apache 2.0 license as described in the file LICENSE.

VERSEIM-2025 REU VERSEIM-2025 REU @ Tufts University 
-/

import Mathlib.Tactic

namespace VERSEIM2025.Subspaces



inductive DisjointUnion (ι κ : Type) where
 | left : ι → DisjointUnion ι κ
 | right : κ → DisjointUnion ι κ

def disjointUnion_funs {ι κ X: Type} ( f₁:ι → X) (f₂:κ → X) (u:DisjointUnion ι κ) : X :=
   match u with
    | DisjointUnion.left x => f₁ x 
    | DisjointUnion.right y => f₂ y


theorem lin_indep_of_orthog (V : Type) [AddCommGroup V] [Module ℝ V] (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
  (hp:PosDef V β) (W₁ W₂ : Submodule ℝ V) (ho:OrthogSubspaces ℝ V β W₁ W₂) 
  (ι₁ ι₂: Type) [Fintype ι₁] [Fintype ι₂] 
  (f₁:ι₁ → V) (f₂:ι₂ → V)
  (hi₁:LinearIndependent ℝ f₁) (hi₂:LinearIndependent ℝ f₂) : 
  LinearIndependent ℝ (disjointUnion_funs f₁ f₂) := by sorry


