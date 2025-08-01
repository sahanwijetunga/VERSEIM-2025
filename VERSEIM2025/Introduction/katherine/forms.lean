
import Mathlib.Tactic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import VERSEIM2025.Forms.BilinearForms

open BilinearForms -- This is the namespace in VERSEIM2025.Forms.Hyperbolic.BilinearForms
open LinearMap.BilinForm
open LinearMap (BilinForm)

-- Let's get started trying to formalize some results in linear algebra
-- about bilinear forms!

-- As a first step, we should formalize the proof that there is -- up to
-- the right notion of conjugacy -- only one non-degenerate alternating
-- form on an even dimensional vector space (and that no such form exists
-- on any odd dimensional vector space). This statement is true for any
-- field whatsoever.  (Corresponding statements for symmetric forms are
-- more complicated -- in particular, the description of conjugacy
-- classes of symmetric forms depends on the field -- so the alternating
-- case seems a good place to start).

-- We are going to work with a finite vector space over a field \(k\):

variable (k : Type) [ Field k ]
variable (V : Type) [ AddCommGroup V ] [ Module k V ]
                    [ FiniteDimensional k V ]

variable (W : Type) [ AddCommGroup W ] [ Module k W ]
                    [ FiniteDimensional k W ]


-- You can read about the `FiniteDimensional` typeclass in §12 of [Math
-- in Lean].

-- You should read about how Lean represents a basis of our vector space(s):

variable {ι : Type} (B : Basis ι k V) [DecidableEq ι] [Fintype ι]
--terms i : ι index the basis vectos `B i`
noncomputable
example (i: ι) : V := B i
-- B i is a vector in V

variable {μ : Type} (C : Basis μ k W) [DecidableEq μ] [Fintype μ]

-- Read this as: "`B` is a basis for the `k`-vector space `V` with
-- index set `ι`".

-- N.B. I haven't understood (or more likely: have forgotten) how to
-- deduce the finiteness of our index set `ι` from the
-- `FiniteDimensional` hypotheses. Maybe you can work this out?

-- There are two ways of stipulating that ι is finite:
-- [Finite ι] and [FinType ι]

--

-- Bilinear forms are precisely terms of type `V →ₗ[k] V →ₗ[k] k`

-- think this through!!

-- **task**

-- prove something like the following:



-- One goal: show that the for the basis `B`, give a bilinear form
-- `β:V →ₗ[k] V →ₗ[k] k` is the same as to give an `ι` by `ι` matrix
-- `M`

-- and once we do that, we can give the definition that β is
-- non-degenerate just in case `M` is `Invertible` (there is an
-- `Invertible` typeclass you can read about in §10.4.1 of
-- [Math-in-lean].

-- Before trying to prove that, we should understand the similar
-- statement that to give a linear mapping `T:V →ₗ[k] V` is the same
-- as to give an `ι` by `ι` matrix.

-- For types `I` and `J`, an `I` by `J` matrix over `k` is essentially
-- a term of type `I → J → k`, though there is actually a type
-- `Matrix`

-- here is the type of n × m matrices for natural numbers n,m

example (m n : ℕ) : Type := Matrix (Fin n) (Fin m) k

-- under the hood this is just `Fin n → Fin m → k` but having a new
-- name lets `Matrix (Fin n) (Fin m)` have possibly-different
-- instances than `Fin n → Fin m → k`

-- for types I and J, here is the type of I × J matrices with
-- coefficients in our field k

example (I J : Type) : Type := Matrix I J k


-- We need a good understanding of what it means that `B.constr k` (or
-- `Basis.constr B k`) gives a linear equivalence between `ι → W` and
-- `V →ₗ[k] W`

noncomputable
example : (ι → W) ≃ₗ[k] V →ₗ[k] W := B.constr k

-- On top of this construction, there is a linear equivalence


open LinearMap

noncomputable
example : (V →ₗ[k] W) ≃ₗ[k] Matrix μ ι k := toMatrix B C

#check (LinearMap.toMatrix B C : (V →ₗ[k] W) ≃ₗ[k] Matrix μ ι k)


-- this should be read " the vector space of linear maps V → W is
-- equivalent to the vector space of μ × ι matrices ".

-- the desired isomorphism between "bilinear forms on V" and square
-- matrices should be defined in essentially the same way as
-- `Basis.constr` (or maybe: *using* `Basis.const` somehow).


-- Let's make a definition (mainly to avoid typing all the arrows).

@[simp]
def Bilinear (V:Type) (k:Type) [Field k] [AddCommGroup V] [Module k V] : Type
  := V →ₗ[k] V →ₗ[k] k

-- Task 1.
-- ======

-- given a basis B of V, we want to define

-- a mapping

/-def Bilinear.toMatrix (V:Type) (k:Type) (B: Basis ι k V) (β:Bilinear V k) : Matrix ι ι k :=
  sorry -/

-- and eventually we want to prove this mapping "is" a linear
-- equivalence.

-- Task 2.
-- ======

-- formulate theorems confirming the linearity properties of our
-- Bilinear terms

-- (it looks to me like the simplifier tactic can prove them).

--  β.toFun (t•x + y) z = t•β.toFun x z + β.toFun y z

-- and

--  β.toFun x (t•y + z) = t•β.toFun x y + β.toFun x z

-- Task 3.
-- ======

-- define a structure

-- structure Alternating V k

-- which has a carrier field which is a bilinear form and has a proof
-- that the given form is alternating, where that should be defined to mean
-- ∀ x, carrier x x = 0


-- Task 4.
-- ======

-- formulate and prove the theorem that

-- β x x = 0 → β x y = - β y x

-- we also need to show that if the characteristic of k is not 2, the
-- converse holds. We'll need to read about the characteristic to do
-- this, but the above implication should work without knowing about
-- this...

-- proposition 2.6 as a lemma
lemma proptwopointsix {B: BilinForm k V} {u v w : V}
(h : ∀ (u v w : V), (((B u) v) * ((B w) u)) = (((B v) u) * ((B u) w))): B.IsAlt ∨ B.IsSymm := by
  have h₀: (((B v) v) *((B w) v) - (((B v) v) * ((B v) w))) = 0 := by
    refine sub_eq_zero_of_eq ?_
    rw[h]
  by_contra j
  simp at j
  unfold BilinForm.IsAlt at j



  sorry



theorem refl_is_alt_or_symm {B: BilinForm k V} {u v w : V} (h: B.IsRefl) [FiniteDimensional k V] :
    B.IsAlt  ∨ B.IsSymm := by
    let x := ((B u) v) • w - (((B u) w) •  v)
    have h₀ : (B u) x = (((B u) v) * ((B u) w)) - (((B u) w) * ((B u) v)) := by
      aesop
    have h₁ : (((B u) v) * ((B u) w)) - (((B u) w) * ((B u) v)) = 0 := by
      rw[mul_comm]
      simp
    rw[h₁] at h₀
    have h₂ :(B x) u =  (((B u) v) * ((B w) u)) - (((B v) u) * ((B u) w)):= by
      sorry
    have h₃ : ∀ (u v w : V), (((B u) v) * ((B w) u)) = (((B v) u) * ((B u) w)) := by
      intro x y z
      have h₃₀ : (B x) y * (B z) x = (B y) x * (B x) z ↔ (((B x) y) * ((B z) x)) - (((B y) x) * ((B x) z)) = 0 := by
        constructor
        · aesop
        · intro g

          sorry


      sorry
    apply proptwopointsix
    · exact u
    · exact v
    · exact w
    · exact h₃



-- construct the iff as well
