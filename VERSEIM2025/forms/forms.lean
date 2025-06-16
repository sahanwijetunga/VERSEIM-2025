
import Mathlib.Tactic


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


-- You can read about the ~FiniteDimensional~ typeclass in \S12 of [Math
-- in Lean].

-- You should read about how Lean represents a /basis/ of our vector space:

variable {ι : Type} (B : Basis ι k V)
variable {κ : Type} (C : Basis κ k W)

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

-- here is the type of n × n matrices for natural numbers n,m

example (m n : ℕ) : Type := Matrix (Fin n) (Fin m) k

-- under the hood this is just `Fin n → Fin m → k` but having a new
-- name lets `Matrix (Fin n) (Fin m)` have different instances than
-- `Fin n → Fin m → k`

-- for types I and J here is the type of I × J matrices with
-- coefficients in our field k

example (I J : Type) : Type := Matrix I J k


-- We need a good understanding of what it means that `B.constr k` (or
-- `Basis.constr B k`) gives a linear equivalence between `ι → W` and
-- `V →ₗ[k] W`

noncomputable
example : (ι → W) ≃ₗ[k] V →ₗ[k] W := B.constr k

-- the desired isomorphism between "bilinear forms on V" and square
-- matrices should be defined in essentially the same way as
-- `Basis.constr` (or maybe: *using* `Basis.const` somehow).
