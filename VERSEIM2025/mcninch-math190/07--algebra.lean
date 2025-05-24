/-
Copyright (c) 2024 George McNinch. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Author : George McNinch
-/

/-
course: Math 190 - Tufts University
instructor: George McNinch
semester: 2024 Spring
-/

import Mathlib.Tactic

<<<<<<< HEAD
--------------------------------------------------------------------------------
-- 07 --Algebra (Linear algebra)
--------------------------------------------------------------------------------

-- We've seen a bit about using `structures` and `classes`to create
-- objects representing common mathematical abstractions in `Lean`.
-- Here I want to explore some of these ideas in the context of *linear algebra*.

-- but let me start by developing some of the API for *groups* and their subgroups

-- For the same reason that a subset is not a type, a subgroup is not a group.
-- If `G` is a group -- i.e.

variable (G : Type) [Group G]


-- then the type of all subgroups of `G` is written `Subgroup G`. Thus
-- to specify a subgroup `H` of `G` one says:

variable (H : Subgroup G)

-- Now, the group `G` is written multiplicatively, otherwise, you'd
-- specify `AdditiveGroup` like this (I'm including a `CommGroup`
-- instance because to me additive groups should be commutative...).

variable (A : Type) [AddGroup A] [CommGroup A]

variable (B : Subgroup A)

-- now the multiplicative group `G` has a *multiplicative 


=======
import Mathlib.Algebra.BigOperators.Ring

--------------------------------------------------------------------------------
-- 07 -- Algebra
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
section MyGroups

-- Recall that we endow a group structure on a type via the notion of "typeclass". 

-- We've seen that a subset is not a type. For the same reason, as subgroup is not a "group"

variable (G : Type) [Group G]

variable (A : Type) [AddCommGroup A]  -- to me, additive groups ought to always be commutative...but `mathlib` does have a typeclass `AddGroup`

variable (H I J : Subgroup G)

variable (B C D : AddSubgroup A)

-- basic properties

open Subgroup

example : ( 1 : G) ∈ H := one_mem _

example : ( 0 : A) ∈ B := zero_mem _

example ( ha : a ∈ H) : a⁻¹ ∈ H := inv_mem ha

example ( hx : x ∈ B) : -x ∈ B := neg_mem hx

example (ha : a ∈ H) (hb : b ∈ H) : a*b ∈ H := mul_mem ha hb

example (hx : x ∈ B) (hy : y ∈ B) : x + y ∈ B := add_mem hx hy

-- in addtive group, can rewrite `subtraction` via negation

example (x y : A) : x - y = x + -y :=  sub_eq_add_neg _ _ 



example (ha : a ∈ H) (hb : b ∈ H) : a*b⁻¹ ∈ H := by 
  apply inv_mem at hb
  apply mul_mem 
  repeat assumption

-- I'm putting the next one in the *exercises*

example (hx : x ∈ B) (hy : y ∈ B) : a - b ∈ B := by sorry
  

-- the following is actually a result in the `mathlib` called `Subgroup.inv_mem_iff`
-- but we can just prove it directly

example : a⁻¹ ∈ H ↔ a ∈ H := by
  constructor
  · intro hi 
    apply inv_mem at hi
    rw [inv_inv] at hi 
    assumption
  · intro ha
    apply inv_mem _
    assumption
  done


-- this one is similar and I've put it in the exericse

example : x ∈ B ↔ -x ∈ B := by 
  sorry

-- I'm putting the next one in the *exercise*
-- it is also already a theorem in `mathlib` named `Subgroup.mul_mem_cancel_left`

example (ha : a ∈ H) : a * b ∈ H ↔ b ∈ H := by
  sorry

example (hx : x ∈ B) : x + y ∈ B ↔ y ∈ B := by
  sorry

-- lattice structure on subgroups

example : CompleteLattice (Subgroup G) := by
  infer_instance

example : CompleteLattice (AddSubgroup A) := by
  infer_instance

-- The "type class inference system" (the system which deals with square bracket inputs to
-- functions) already knows this. The `infer_instance` tactic means "find this
-- construction in the database".

-- as a consequence, every group has a "smallest subgroup" `⊥` and a "largest subgroup"
-- `⊤`

example : x ∈ (⊥ : AddSubgroup A) ↔ x = 0 := AddSubgroup.mem_bot

example (x : A) : x ∈ (⊤ : AddSubgroup A) := AddSubgroup.mem_top _

-- Conjugation of a subgroup

-- If `x:G` and `H : Subgroup G` We are going to define the conjugate
-- `xHx⁻¹`, a term of type `Subgroup G`.

-- The *set* `xHx⁻¹` is defined by
-- `{ a : g ∣ ∃ b, b ∈ H ∧ a = x * a * x⁻¹ }`
-- so we need to show that this set satisfies the axioms for a subgroup.

variable { G H } 

variable {x y z : G}

theorem conj.one_mem : (1:G) ∈ {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹} := by
   use 1
   constructor
   · exact Subgroup.one_mem H
   · group

theorem conj.inv_mem (hy : y ∈ {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹}) :
  y⁻¹ ∈ {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹} := by
  rcases hy with ⟨h,he,rfl⟩  -- putting `rfl` here simplifies things a bit...
  use h⁻¹, inv_mem he
  group
    

theorem conj.mul_mem (hy : y ∈ {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹})
  (hz : z ∈ {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹}) :
  y * z ∈ {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹} :=  by
  rcases hy with ⟨g,hg,rfl⟩
  rcases hz with ⟨k,hk,rfl⟩
  use g * k, mul_mem hg hk
  group

-- now we can define a *conjugate operation*

open Subgroup 

def conjugate (H : Subgroup G) (x: G) : Subgroup G 
  where
  carrier := { a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹ }
  one_mem' := conj.one_mem
  inv_mem' := conj.inv_mem
  mul_mem' := conj.mul_mem
  
  

end MyGroups
--------------------------------------------------------------------------------

section MyLinAlg

variable (K : Type) [Field K]

-- a Vector Space is just a Module for `K`.

--------------------------------------------------------------------------------
-- class Module (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] extends DistribMulAction :
-- Type (max u v)

-- A module is a generalization of vector spaces to a scalar
-- semiring. It consists of a scalar semiring R and an additive monoid
-- of "vectors" M, connected by a "scalar multiplication" operation r
-- • x : M (where r : R and x : M) with some natural associativity and
-- distributivity axioms similar to those on a ring.

--     smul : R → M → M
--     one_smul : ∀ (b : M), 1 • b = b
--     mul_smul : ∀ (x y : R) (b : M), (x * y) • b = x • y • b
--     smul_zero : ∀ (a : R), a • 0 = 0
--     smul_add : ∀ (a : R) (x y : M), a • (x + y) = a • x + a • y
--     add_smul : ∀ (r s : R) (x : M), (r + s) • x = r • x + s • x
--------------------------------------------------------------------------------

variable (V: Type) [AddCommGroup V] [Module K V]

-- Now, elements of the field `K` act on the vector space `V` by
-- `hSMul` (`heterogeneous scalar multiplication`), or the symbol `•`
-- (typed "\smul").

example (α : K) (v : V) : V := α • v

-- now subspaces of `V` are elements of the type `Subspace K V`

variable (X Y : Subspace K V)

-- note that `X ⊆ Y` is defined -- this only works for `Set V`.

-- but once again the `Subspaces` form a complete lattice


example : CompleteLattice (Subspace K V) := by
  infer_instance

-- And as for any complete lattice, the relation `≤` is defined.

example (hx : x ∈ X) (hc : X ≤ Y) : x ∈ Y := hc hx

-- use the lattice operation `⊓` ("\glb") instead of `∩`

-- of course, there is no union operation on subspaces; `⊔` ("\lub")
-- is the *sum* of subspaces

-- also `⊥` is the 0-dimensional subspace and `⊤` is V considered as a
-- subspace of itself.

-- let's consider another vector space

variable (W: Type) [AddCommGroup W] [Module K W]

-- the `K`-linear maps from `V` to `W` are terms of type `V →ₗ[K] W`, which is notation
-- for `LinearMap (RingHom.id K) V W`
-- these terms are additive group homomorphisms `φ:V → W` for which
-- φ(a • v) = (id a) • (φ v)

variable ( φ ψ : V →ₗ[K] W ) 
variable ( x : V)

example (x : V) : W := φ x

example (X : Subspace K V) : Subspace K W :=
  Submodule.map φ X
  --or:
  -- X.map φ

example (X : Subspace K V) (Y : Subspace K W) (hx: x ∈ X) (hY : Submodule.map φ X ≤ Y) : (φ x) ∈ Y := by 
  apply hY
  apply Submodule.mem_map.mpr
  use x

open Submodule 
-- let's try this:
example (X : Subspace K V) (Y : Subspace K W) : map φ X ≤ Y ↔ X ≤ comap φ Y := by
  constructor
  · intro h x hx
    apply mem_comap.mpr 
    apply h
    apply mem_map.mpr 
    use x
  · intro h y hm
    rw [mem_map] at hm
    rcases hm with ⟨x,hx,heq⟩
    rw [←heq]
    apply h
    assumption


-- here is how to say "let V be a finite dimensional vector space"

variable (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V]


-- prove that if `V` is a 5-dimensional vector space and `A, B` are
-- two subspaces of dimension 3, then the intersection `A ∩ B` - or
-- rather, `A ⊓ B` - cannot be the zero vector space.

-- `FiniteDimensional.finrank V` is the dimension of `V`
open FiniteDimensional -- now we can just write `finrank`. 

-- note that since a subspace `X : Subspace V` isn't a type, you can't *really* speak of `finrank K X`.
-- But you can *coerce* X into a type `↥X : Type [Vectorspace K X]`.
-- type "↥" with "\u-|"
-- so you can write `finrank K ↥X`
-- but lean allows you to abbreviate `finrank K X` for `finrank K ↥X`
-- (note that in the *lean context*, the type appears with the ↥ symbol...)

example (A B : Subspace K V) (hV : finrank K V = 5) (hA : finrank K A = 3) (hB : finrank K B = 3) :
    A ⊓ B ≠ ⊥ := by
    intro h
    have h1 := finrank_sup_add_finrank_inf_eq A B
    rw [hA,hB,h,finrank_bot K V] at h1
    norm_num at h1
    have h2 :=Submodule.finrank_le (A ⊔ B)
    rw [h1, hV] at h2              
    linarith

-- let's define the span of some vectors in V

-- we'll index these vectors by a "finite type"

variable (I : Type) [Fintype I]

variable (f:I → V) (α:I → K)

open scoped BigOperators

open Finset

example : V := ∑ i, (α i) • (f i)

lemma mul_sum'  {f : I → V} {a : K} :
    a • (∑ i, f i) = ∑ i, a • (f i) := 
  map_sum (AddMonoidHom.smulLeft a) _ _


example (α β : I → K) : ∑ i, α i + ∑ i, β i = ∑ i, ((α i) + (β i)) := by
  exact sum_add_distrib.symm


def span' {I: Type} [Fintype I ] { K : Type } [Field K]  {V : Type} [AddCommGroup V] [ Module K V ]
   (f : I → V) : Subspace K V 
  where
    carrier := { v : V | ∃ (α:I → K), v = ∑ i, (α i) • (f i) }
    add_mem' := by  
      intro a b ha hb
      rcases ha with ⟨α,haeq⟩
      rcases hb with ⟨β,hbeq⟩
      use α + β
      rw [haeq,hbeq]
      rw [ sum_add_distrib.symm ]
      simp [ map_sum ] 
      apply sum_congr 
      · triv
      · intro x _
        rw [ add_smul ]      
    zero_mem' := by 
      use (λ _ => 0)
      field_simp
    smul_mem' := by 
      intro c x hx
      simp at hx
      simp
      rcases hx with ⟨β,heq⟩ 
      use (λ i => c * β i)
      rw [ heq]
      rw [ mul_sum' ]
      apply sum_congr
      · triv
      · intro x _
        rw [ smul_smul ]

-- example

noncomputable section

example : Module ℚ (Fin 3 → ℚ) := by
   infer_instance
  
def kron : Fin 3  →  Fin 3 → ℚ
  | 0, 0 => 1
  | 1, 1 => 1 
  | 2, 2 => 1
  | _, _ => 0

def e (i : Fin 3) : Fin 3 → ℚ := kron i
  
#check e 0 + e 1

def F : Fin 2 → (Fin 3 → ℚ)
  | 0 => (e 0) + (e 1)
  | 1 => e 1 + e 2


#check span' F

def M : Subspace ℚ (Fin 3 → ℚ) := span' F 

end 

end MyLinAlg

>>>>>>> 4029744e76473f77f549b88f571e6f0170cee352
