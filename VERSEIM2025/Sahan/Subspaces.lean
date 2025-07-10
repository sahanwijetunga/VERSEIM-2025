
-- --------------------------------------------------------------------------------
-- /-
-- Copyright (c) 2025 Clea Bergsman, Katherine Buesing, George McNinch, Sahan Wijetunga. All rights reserved.

-- Released under the Apache 2.0 license as described in the file LICENSE.

-- VERSEIM-2025 REU VERSEIM-2025 REU @ Tufts University
-- -/

-- import Mathlib.Tactic
-- import VERSEIM2025.Sahan.BilinearForms

-- --------------------------------------------------------------------------------

-- inductive DisjointUnion (ι κ : Type) where
--  | left : ι → DisjointUnion ι κ
--  | right : κ → DisjointUnion ι κ

-- def disjointUnion_funs {ι κ X: Type} ( f₁:ι → X) (f₂:κ → X) (u:DisjointUnion ι κ) : X :=
--    match u with
--     | DisjointUnion.left x => f₁ x
--     | DisjointUnion.right y => f₂ y


-- open DisjointUnion
-- def fin_disjoint_fin_equiv_fin (n m: ℕ) : DisjointUnion (Fin n) (Fin m) ≃ Fin (n+m) where
--   toFun := fun i =>
--     match i with
--     | left x => Fin.castAdd m x
--     | right x => by
--         rw [ add_comm ]
--         exact Fin.castAdd n x
--   invFun := by
--     rintro ⟨i,_⟩
--     if h : i < n then
--        have : NeZero n := NeZero.mk (by linarith)
--        exact left (Fin.ofNat n i)
--     else
--        have : NeZero m := NeZero.mk (by linarith)
--        exact right (Fin.ofNat m (n-i))
--   left_inv := by sorry
--   right_inv := by sorry


-- --------------------------------------------------------------------------------

-- theorem lin_indep_by_transverse_subspaces
--    (k V : Type) [Field k] [AddCommGroup V] [Module k V] (I₁ I₂ : Type)
--    (b₁ : I₁ → V) (b₂ : I₂ → V)
--    (b1_indep : LinearIndependent k b₁)
--    (b2_indep : LinearIndependent k b₂)
--    (W₁ W₂ : Submodule k V)
--    (h_int : W₁ ⊓ W₂ = ⊥)
--    (hbw1 : ∀ i, b₁ i ∈ W₁)
--    (hbw2 : ∀ i, b₂ i ∈ W₂)
--    : LinearIndependent k (disjointUnion_funs b₁ b₂) := by sorry



-- --------------------------------------------------------------------------------
