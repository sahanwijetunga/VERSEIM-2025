--------------------------------------------------------------------------------
/-
Copyright (c) 2025 George McNinch. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Clea Bergsman, Katherine Buesing, George McNinch, Sahan Wijetunga
-/

/- VERSEIM-2025 REU -/

import Mathlib.Tactic

-- recall we introduced the disjoint union

inductive DisjointUnion (ι₁ ι₂ : Type) where
 | left : ι₁ → DisjointUnion ι₁ ι₂
 | right : ι₂ → DisjointUnion ι₁ ι₂

def disjointUnion_funs {ι₁ ι₂ X: Type} ( f₁:ι₁ → X) (f₂:ι₂ → X) (u: ι₁ ⊕ ι₂) : X :=
   match u with
    | Sum.inl x => f₁ x
    | Sum.inr y => f₂ y


-- here are some statements about disjoint_union that should be established

-- first establish an equivalence of types between the disjoint union
-- of `Fin n` and `Fin m` with the type `Fin (n+m)`

-- We define the `toFun` of our equivalence as follows:

-- terms of the form `left x` where `(x:Fin n)` is sent to `(x:Fin (n + m))`

-- and terms of the form `right x` where `(x:Fin m)` is sent to
-- `(x + n : Fin(n+m))`

-- the summation is accomplished via `Fin.castAdd`

#check Fin.castAdd

-- ** exercise ** you'll need to define the remaining components of
-- the structure determining the equivalence.

open DisjointUnion in
def invFun (n m :ℕ) : Fin (n+m) → DisjointUnion (Fin n) (Fin m) := by
  rintro ⟨i,_⟩  -- here (i:ℕ) is the underlying Nat of the Fin (n+m) argument
  if i < n then
     have : NeZero n := NeZero.mk (by linarith)
     exact left (Fin.ofNat n i)
  else
     have : NeZero m := NeZero.mk (by linarith)
     exact right (Fin.ofNat m (n-i))

open DisjointUnion

def fin_disjoint_fin_equiv_fin (n m: ℕ) : (Fin n) ⊕ (Fin m) ≃ Fin (n+m) where
  toFun := fun i =>
    match i with
    | Sum.inl x => Fin.castAdd m x
    | Sum.inr x => by
        rw [ add_comm ]
        exact Fin.castAdd n x
  invFun := by
    rintro ⟨i,_⟩  -- here (i:ℕ) is the underlying Nat of the Fin (n+m) argument
    if i < n then
      have : NeZero n := NeZero.mk (by linarith)
      exact Sum.inl (Fin.ofNat n i)
    else
      have : NeZero m := NeZero.mk (by linarith)
      exact Sum.inr (Fin.ofNat m (n-i))
  left_inv := by
    intro x₀
    match x₀ with
    | Sum.inl y => simp
    | Sum.inr z =>
    simp
    sorry
  right_inv := by
    intro ⟨ x₀, h₁⟩
    simp
    sorry


#check Fin.castAdd
#check Fin.toNat
--------------------------------------------------------------------------------

-- this result is perhaps what should be proved first before proving
-- the result I earlier described as `lin_indep_of_orthog`.


lemma disjoint_union_sum (I₁ I₂ : Type) [Fintype I₁] [Fintype I₂]
(k V : Type) [Field k] [AddCommGroup V] [Module k V]
(a : I₁ ⊕ I₂ → V) : ∑ i : I₁ ⊕ I₂, a i = ∑ j : I₁, a (Sum.inl j) + ∑ k : I₂, a (Sum.inr k) := by
  exact Fintype.sum_sum_type a


theorem lin_indep_by_transverse_subspaces
   (k V : Type) [Field k] [AddCommGroup V] [Module k V] (I₁ I₂ : Type)
   [Fintype I₁] [Fintype I₂]
   (b₁ : I₁ → V) (b₂ : I₂ → V)
   (b1_indep : LinearIndependent k b₁)
   (b2_indep : LinearIndependent k b₂)
   (W₁ W₂ : Submodule k V)
   (h_int : W₁ ⊓ W₂ = ⊥)
   (hbw1 : ∀ i, b₁ i ∈ W₁)
   (hbw2 : ∀ i, b₂ i ∈ W₂)
   [DecidableEq I₁] [DecidableEq I₂]
   : LinearIndependent k (disjointUnion_funs b₁ b₂) := by
    rw[linearIndependent_iff'']
    intro s a g h₁ h₂
    have k₀ : ∑ i ∈ s, a i • disjointUnion_funs b₁ b₂ i = ∑ i : (I₁ ⊕ I₂), a i • disjointUnion_funs b₁ b₂ i := by
      rw[h₁]
      have k₀₀ : Disjoint s sᶜ := by
        unfold Disjoint
        intro x₀
        simp
        sorry
      have k₀₁ : s ∪ sᶜ = (⊤ : Finset (I₁ ⊕ I₂)) := by
        simp
      have k₀₂ : (⊤: Finset (I₁ ⊕ I₂)) = Finset.univ := by
        simp
      rw[k₀₂] at k₀₁
      rw[ ← k₀₁]
      rw[Finset.sum_union k₀₀]
      rw[h₁]
      -- rw[← Set.mem_compl] -> this is exactly what i want to do, but its inside of sum
      sorry
    have eq_h : ∑ a₁, a (Sum.inl a₁) • disjointUnion_funs b₁ b₂ (Sum.inl a₁) +
    ∑ a₂, a (Sum.inr a₂) • disjointUnion_funs b₁ b₂ (Sum.inr a₂) =
    ∑ i, (a (Sum.inl i)) • (b₁ i) + ∑ j, (a (Sum.inr j)) • (b₂ j) := by
      unfold disjointUnion_funs
      simp
    have k₁ : ∑ i, (a (Sum.inl i)) • (b₁ i) = - ∑ j, (a (Sum.inr j)) • (b₂ j)  := by
      rw[k₀] at h₁
      simp at h₁
      rw[eq_h] at h₁
      sorry
    have k₂ : ∑ i, (a (Sum.inl i)) • (b₁ i) ∈ W₁ ⊓ W₂ := by
      simp
      have k₂₀ : ∑ i, (a (Sum.inl i)) • (b₁ i) ∈ W₁ := by
        exact Submodule.sum_smul_mem W₁ (fun i ↦ a (Sum.inl i)) fun c a ↦ hbw1 c
      have k₂₁ : ∑ i, (a (Sum.inl i)) • (b₁ i) ∈ W₂ := by
        rw[k₁]
        apply Submodule.neg_mem
        exact Submodule.sum_smul_mem W₂ (fun i ↦ a (Sum.inr i)) fun c a ↦ hbw2 c
      constructor
      · exact k₂₀
      · exact k₂₁
    have k₃ : - ∑ j, (a  (Sum.inr j)) • (b₂ j) ∈ W₁ ⊓ W₂ := by
      rw[k₁] at k₂
      exact k₂
    rw[linearIndependent_iff] at b1_indep
    rw[linearIndependent_iff] at b2_indep
    rw[h_int] at k₂
    rw[h_int] at k₃
    simp at k₂
    simp at k₃
    sorry
    -- a is coefficients, b1 (x) is the vectors, b2 (x) is the other vectors
    -- step zero: make a hypothesis that b1a1 = -b2a2 and then show =>
    -- step one: show its in the intersection
    -- step two: the intersection is zero.
