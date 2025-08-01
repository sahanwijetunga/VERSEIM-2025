--------------------------------------------------------------------------------
/-
Copyright (c) 2025 George McNinch. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Clea Bergsman, Katherine Buesing, George McNinch, Sahan Wijetunga
-/

/- VERSEIM-2025 REU -/

import Mathlib.Tactic

-- I had a thought yesterday evening that it is perhaps easier to
-- start with symmetric bilinear forms, despite their eventual greater
-- comlpexity.

-- e.g. you probably saw what is known as "Gram-Schmidt" in your
-- linear algebra class. So let's implement that!

-- We need some notions about bilinear forms.

-- remember that `V →ₗ[k] V →ₗ[k] k` is the type of bilinear mappings on the vector space `V`

-- lets define predicates for *symmetric* and *alternating* bilinear forms

def BilSymmetric {k V : Type} [AddCommGroup V] [Field k] [Module k V] (β:V →ₗ[k] V →ₗ[k] k)  : Prop :=
  ∀ (x y : V), β x y = β y x

def BilAlternating {k V : Type} [AddCommGroup V] [Field k] [Module k V] (β:V →ₗ[k] V →ₗ[k] k)  : Prop :=
  ∀ (x : V), β x x = 0

def BilAlternating' {k V : Type} [AddCommGroup V] [Field k] [Module k V] (β:V →ₗ[k] V →ₗ[k] k)  : Prop :=
  ∀ (x y : V), β x y = - β y x

-- *for the time being* we are going to work with k = ℝ

-- we work with a real vector space:

variable {V : Type} [AddCommGroup V] [Module ℝ V ]

-- and we suppose V has a finite basis indexed by the finite type ι (\iota)

variable (b : Basis ι ℝ V) [Fintype ι]


-- Next, let β be a symmetric bilinear form on V

variable (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
variable (beta_symm : BilSymmetric β)

-- Finally, we are going to suppose that β is *positive definite*

def PosDef (V : Type) [AddCommGroup V] [Module ℝ V] (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ) : Prop :=
  ∀ x : V, β x x ≥ 0 ∧ x ≠ 0 → β x x > 0

-- the positive definite assumption implies that β is non-degenerate,
-- but is an "easier" assumption to reason about. That is the main
-- reason I think it is a good idea to consider this case first!

--

-- Our goal wil be to show that V has an orthogonal basis

-- more generally we say that for a type `I`, a function `f:I → V` is
-- orthogonal with respect to β if for each (i j : I) we have

-- `i ≠ j → β (f i) β (f j) = 0`.

-- let's make a predicate for orthogonal bases

@[simp]
def OrthogBasis (V : Type) [AddCommGroup V] [ Module ℝ V] (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
  (c:Basis I ℝ V) : Prop := ∀ (i j : I), i ≠ j → β (c i) (c j) = 0

-- here is our target Theorem

theorem posdef_has_orthog_basis (V : Type) [AddCommGroup V] [ Module ℝ V ]
  ( b: Basis ι ℝ V ) [Fintype ι] (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hp:PosDef V β)
  : ∃ (c:Basis ι ℝ V), OrthogBasis V β c := by
  unfold OrthogBasis
  sorry

#check Basis.mk

-- I believe the simplest way to prove this will be to use what is
-- known as the *Gram-Schmidt orthogonalization process*.

-- https://en.wikipedia.org/wiki/Gram%E2%80%93Schmidt_process

-- and see [Liesen and Hemrmann, §12.2]

--------------------------------------------------------------------------------

-- Here are some lemmas that I believe we will need (of course, we may
-- need to massage the statements -- and perhaps especially the names!
-- --  but these are a good starting point I think).

-- some of these are general, and so I'll return to more general assumptions

section lemmas

--------------------------------------------------------------------------------

-- 1. the orthogonal complement of a `S:Set V` is a subspace of V

-- in blackboard math, the orthogonal complement of S is often written S^⟂


-- someone needs to give the proofs in the following definition.

def OrthogComplement {k V:Type} [AddCommGroup V] [Field k] [Module k V] (S : Set V)
    {β:V →ₗ[k] V →ₗ[k] k} : Subspace k V where
  carrier := { v | ∀ (x:S), β v x = 0 }
  add_mem' := by
    intro a b ha hb
    dsimp at *
    intro ⟨x, hx⟩
    have hax: β a x = 0 := ha ⟨x, hx⟩
    have hbx: β b x = 0 := hb ⟨x, hx⟩
    have: β (a+b) x = 0  := by
      calc
        β (a+b) x = (β a + β b) x := by
          simp
        _ = β a x + β b x := by rfl
        _ = 0 + 0 := by rw[hax, hbx]
        _ = 0 := by abel
    exact this
  zero_mem' := by
    intro ⟨x, hx⟩
    apply LinearMap.BilinForm.zero_left x
  smul_mem' := by
    rintro c a h
    intro ⟨x, hx⟩
    show β (c• a) x = 0
    calc
      (β (c• a)) x = (c• β a) x := by
        -- simp on its own would also solve
        apply congr_fun _
        refine DFunLike.ext'_iff.mp ?_
        exact LinearMap.map_smul β c a
      _ = c• β a x := by rfl
      _ = c • 0 := by rw[h ⟨x, hx⟩]
      _ = 0 := by rw[smul_zero]

-- you should read in [math-in-lean] §10.2 about `add_mem'` vs `add_mem` etc.

--------------------------------------------------------------------------------

-- 2. Suppoe that W₁ and W₂ are subspaces of a vector space V, and
-- suppose that W₁ and W₂ are orthogonal  to one another.

-- if we have a linearly independent subset of W₁ and a linearly
-- independent subset of W₂, we want to argue that the "union" of
-- these subsets is linearly independent.

-- Lean prefers to talk about linear independence of functions `ι → V`
-- so let's formulate it that way.

-- to start with I'm going to work over ℝ because otherwise we need to
-- assume something about non-degneracy of β on the subspaces W₁ and
-- W₂. The PosDef assumption makes this easy!

-- first, let's make a predicate for "orthogonal"

def OrthogSubspaces (k V:Type) [AddCommGroup V] [Field k] [Module k V] (β:V →ₗ[k] V →ₗ[k] k)
  (W₁ W₂ : Submodule k V) : Prop :=
  ∀ (x:W₁), ∀ (y:W₂), β x y = 0

inductive DisjointUnion (ι₁ ι₂ : Type) where
 | left : ι₁ → DisjointUnion ι₁ ι₂
 | right : ι₂ → DisjointUnion ι₁ ι₂

def disjointUnion_funs {ι₁ ι₂ X: Type} ( f₁:ι₁ → X) (f₂:ι₂ → X) (u:DisjointUnion ι₁ ι₂) : X :=
   match u with
    | DisjointUnion.left x => f₁ x
    | DisjointUnion.right y => f₂ y


theorem lin_indep_of_orthog (V : Type) [AddCommGroup V] [Module ℝ V] (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
  (hp:PosDef V β) (W₁ W₂ : Submodule ℝ V) (ho:OrthogSubspaces ℝ V β W₁ W₂)
  (ι₁ ι₂: Type) [Fintype ι₁] [Fintype ι₂]
  (f₁:ι₁ → V) (f₂:ι₂ → V)
  (hi₁:LinearIndependent ℝ f₁) (hi₂:LinearIndependent ℝ f₂) :
  LinearIndependent ℝ (disjointUnion_funs f₁ f₂) := by sorry


example (f : ι₁ → X) (g : ι₂ → X) : ι₁ ⊕ ι₂ → X :=
  fun x => match x with
    | Sum.inl i₁ => f i₁
    | Sum.inr i₂ => g i₂

--------------------------------------------------------------------------------

-- 3.  direct sum

-- If W₁ and W₁ are subspaces of a vector space, we want to give
-- conditions under which V is the *direct sum*. I believe (hope) that
-- [Liesen and Hemrmann] defines the notion. (I'll check!)

example (x₁ x₂ y₁ y₂: V) [AddCommGroup V] (h: x₁+x₂=y₁+y₂) : x₁-y₁=y₂-x₂:= by
  rw[add_comm y₁ _] at h
  exact sub_eq_sub_iff_add_eq_add.mpr h

theorem direct_sum_unique_repr (k V : Type) [Field k] [AddCommGroup V] [Module k V]
  (W₁ W₂ : Submodule k V) (h_int : ⊥ = W₁ ⊓ W₂)
  (x₁ x₂ y₁ y₂ : V) (h₁ : x₁ ∈ W₁ ∧ y₁ ∈ W₁) (h₂ : x₂ ∈ W₂ ∧ y₂ ∈ W₂ ) :
  x₁ + x₂ = y₁ + y₂ → x₁ = y₁ ∧ x₂ = y₂ := by
    have ⟨hx1, hy1⟩ := h₁
    have ⟨hx2, hy2⟩ := h₂
    intro h
    have h': x₁-y₁ = y₂-x₂ :=
      calc
        x₁-y₁ = (x₁+x₂-x₂)-y₁ := by abel_nf
        _ = (y₁+y₂-x₂)-y₁ := by rw[h]
        _ = y₂-x₂ := by abel
    have hw1: (x₁-y₁) ∈ W₁ := by
      exact (Submodule.sub_mem_iff_left W₁ hy1).mpr hx1
    have hw2: (x₁-y₁) ∈ W₂ := by
      have: y₂-x₂ ∈ W₂ := by
        exact (Submodule.sub_mem_iff_left W₂ hx2).mpr hy2
      rw[h']
      assumption
    have hw: (x₁-y₁) ∈ (W₁: Set V) ∩ W₂ := by
      exact Set.mem_inter hw1 hw2
    have hw0: x₁-y₁ = 0 := by
      have: (W₁: Set V) ∩ W₂ = {(0: V)} := calc
        (W₁: Set V) ∩ W₂ = W₁ ⊓ W₂ := rfl
        _ = (⊥: Submodule k V) := by
          exact congrArg SetLike.coe (id (Eq.symm h_int))
        _ = ({0}: Set V) := rfl
      have: (x₁-y₁) ∈ ({0}: Set V) := by
        rw[<- this]
        assumption
      exact this
    have hxy1: x₁=y₁ := by
      calc
        _ = (x₁-y₁)+y₁ := by abel
        _ = 0+y₁ := by rw[hw0]
        _ = y₁ := by abel
    have hxy2: x₂=y₂ := by
      calc
        x₂ = x₂+ 0 := by abel
        _ = x₂+(x₁-y₁) := by rw[hw0]
        _ = x₂+(y₂-x₂) := by rw[h']
        _ = y₂ := by abel
    exact ⟨hxy1, hxy2⟩
