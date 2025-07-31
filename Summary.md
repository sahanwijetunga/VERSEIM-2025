# Results/Contributions

This is the repository for the *formalization project* of the [2025
VERSEIM-REU](https://sites.tufts.edu/verseimreu/).

- [Forms](/VERSEIM2025/Forms)
  - [Hyperbolic](/VERSEIM2025/Forms/Hyperbolic) - Sahan
    - [Alternating](/VERSEIM2025/Forms/Hyperbolic/Alternating.lean)
      - Nondegenerate alternating bilinear forms are hyperbolic (`alternating_is_hyperbolic`), thus dimension 2n (`alternate_is_even_dimension`), and those which are of equal (finite) dimension are isomorphic (as bilinear form spaces)  (`alternate_iso`)
    - [Basics](/VERSEIM2025/Forms/Hyperbolic/Basics.lean): 
      - States definitions for Hyperbolic forms and theorems relating the different viewpoints of Hyperbolic spaces together. 
    - [Symmetric](/VERSEIM2025/Forms/Hyperbolic/Symmetric.lean)
      - Any nondegenerate symmetric bilinear form is the direct sum of a hyperbolic and anisotropic (definite) form
    - [TwoSpaceBasics](/VERSEIM2025/Forms/Hyperbolic/TwoSpaceBasics.lean)
      - Partially duplicates material from [Basics](/VERSEIM2025/Forms/Hyperbolic/Basics.lean) for easier use in CasselsPfisterTheorem
  - [RationalFunctionFields](/VERSEIM2025/Forms/RationalFunctionFields)
    - [Basics](/VERSEIM2025/Forms/RationalFunctionFields/Basics.lean) - Sahan
      - Contains definitions and results about Quadratic forms, mostly those from `V -> F` extended to `F[X] -> V[X]` and `V(X) -> F(X)`, to state/prove reuslts in [CasselsPfister](/VERSEIM2025/Forms/RationalFunctionFields/CasselsPfister.lean)
      - `QuadraticFormExtensionPolynomial`: `deg Q(v) = 2 * deg v` for `Q:V -> F` (so `v` in `V[X]` and `Q(v)` in `F[X]`)
      - `HyperplaneReflection `: Reflecting vectors across a fixed vector 
      - Various diagrams commute (e.g. `Q: V -> F` extended to `V(X) -> F(X)` agrees with `V[X] -> F[X]` on the common domain)
    - [CasselsPfister](/VERSEIM2025/Forms/RationalFunctionFields/CasselsPfister.lean) - Sahan
      - Proves Cassels-Pfister Theorem: The values taken by the extension of a quadratic map `φ: V → F` to `V(X) → F(X)` that are in `F[X]` are taken by the extension `V[X] → F[X]` as well. (See ["The Algebraic and Geometric Theory
of Quadratic Forms"](https://www.math.ucla.edu/~merkurev/Book/Kniga-final/Kniga.pdf) Theorem 17.3)
    - [PolynomialModule](/VERSEIM2025/Forms/RationalFunctionFields/PolynomialModule.lean) - George
      - Proves an equivalence between two notions of `V[X]`, namely viewed as extension by scalars (a tensor product of `V` with `F[X]` over `F`) and viewed as formal polynomials with coefficients in `V` (e.g. functions `Nat -> V` with finite support)
    - [Results](/VERSEIM2025/Forms/RationalFunctionFields/Results.lean) - Sahan
      - Let `f ∈ F[X]` be a sum of `n` squares in `F(X)`. Then `f` is a sum of `n` squares in `F[X]`
  - [Reflexive](/VERSEIM2025/Forms/RationalFunctionFields)
    - [Alternating_or_Symmetric](/VERSEIM2025/Forms/Reflexive/Alternating_or_Symmetric.lean) - Katherine & Sahan
      - Proves any reflexive bilinear form is alternating or symmetric
    - [Radical](/VERSEIM2025/Forms/Reflexive/Radical.lean)    
      - Given a bilinear form `B: V x V -> F`, defines `rad(B)={v| B(v,w)=0 for all w} ` and a bilinear form on `V/rad(B)` which is nondegenerate and such that the obvious diagram commutes
- [PolynomialModuleDegree](/VERSEIM2025/PolynomialModuleDegree) - Sahan
  - [Definitions](/VERSEIM2025/PolynomialModuleDegree/Definitions.lean) and [Operations](/VERSEIM2025/PolynomialModuleDegree/Operations.lean) mostly achieve results over `V[X]` (the polynomial module) that are achieved for `R[X]` (the polynomial ring) in Mathlib. 
  - [Misc](/VERSEIM2025/PolynomialModuleDegree/Misc.lean) 
    - `V[X]` has no torsion elements over `F[X]`
    - You can perform division in `V[X]` from `F[X]`
- [form_equivalence](/VERSEIM2025/form_equivalence.lean) - Clea
- [applications](/VERSEIM2025/applications.lean) - Katherine
  - `ortho_complement_nondeg
- [Subspaces](/VERSEIM2025/Subspaces.lean) - Katherine
  - lin_ind_by_tran - line 46
  - basis_of_direct_sum - last thing in file


