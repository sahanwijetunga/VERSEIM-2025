--------------------------------------------------------------------------------
/-
Copyright (c) 2025 George McNinch. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Clea Bergsman, Katherine Buesing, George McNinch, Sahan Wijetunga
-/

/- VERSEIM-2025 REU -/

import Mathlib.Tactic

-- recall we introduced the disjoint union

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

example (n: ℕ): (n ≤ 2) ∨ (n > 2) := by exact le_or_lt n 2

-- #check Fin.

def invFun (n m :ℕ) : Fin (n+m) → (Fin n) ⊕ (Fin m) := by
  rintro ⟨i,_⟩  -- here (i:ℕ) is the underlying Nat of the Fin (n+m) argument
  if i < n then
     have : NeZero n := NeZero.mk (by linarith)
     left
     exact Fin.ofNat n i
  else
     have : NeZero m := NeZero.mk (by linarith)
     right
     exact Fin.ofNat m (n-i)

def forwardFun (n m :ℕ) : Fin n ⊕ Fin m → Fin (n+m) :=
  fun i =>
    match i with
    | Sum.inl x => Fin.castAdd m x
    | Sum.inr x => by
        rw [ add_comm ]
        exact Fin.castAdd n x


def fin_disjoint_fin_equiv_fin' (n m: ℕ) : Fin n ⊕ Fin m ≃ Fin (n+m) where
  toFun := forwardFun n m
  invFun :=
    invFun n m
  left_inv := by
    unfold Function.LeftInverse
    intro A
    unfold invFun
    unfold forwardFun
    simp
    sorry
  right_inv := by sorry

def invFun' (n m :ℕ) : Fin (n+m) → Fin n ⊕ Fin m:= by
  rintro ⟨i,_⟩  -- here (i:ℕ) is the underlying Nat of the Fin (n+m) argument
  if i < n then
     have : NeZero n := NeZero.mk (by linarith)
     exact Sum.inl (Fin.ofNat n i)
  else
     have : NeZero m := NeZero.mk (by linarith)
     exact Sum.inr (Fin.ofNat m (n-i))

--------------------------------------------------------------------------------

-- this result is perhaps what should be proved first before proving
-- the result I earlier described as `lin_indep_of_orthog`.

theorem lin_indep_by_transverse_subspaces
   (k V : Type) [Field k] [AddCommGroup V] [Module k V] (I₁ I₂ : Type)
   (b₁ : I₁ → V) (b₂ : I₂ → V)
   (b1_indep : LinearIndependent k b₁)
   (b2_indep : LinearIndependent k b₂)
   (W₁ W₂ : Submodule k V)
   (h_int : W₁ ⊓ W₂ = ⊥)
   (hbw1 : ∀ i, b₁ i ∈ W₁)
   (hbw2 : ∀ i, b₂ i ∈ W₂)
   : LinearIndependent k (Sum.elim b₁ b₂) := by sorry
