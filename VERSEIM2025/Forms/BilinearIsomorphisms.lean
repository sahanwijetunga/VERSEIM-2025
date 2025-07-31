--------------------------------------------------------------------------------
/-
Copyright (c) 2025 Clea Bergsman, Katherine Buesing, George McNinch, Sahan Wijetunga. All rights reserved.

Released under the Apache 2.0 license as described in the file LICENSE.

VERSEIM-2025 REU @ Tufts University
-/

import VERSEIM2025.Forms.Bilinear
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-
  The purpose of this file is to define an isomorphism of bilinear formed spaces

  Notable Definitions
  - EquivBilin

  Major Results (Completed):
  - Proof (construction) that two spaces (V,β) (V',β') over k are isomorphic from
    a bijection of bases(really type equivalence) that commutes with the bilinear form
    `EquivBilin_of_basis_equiv`

  Major Results (Planned):
  - Construct a bilinear form on (arbitrary) direct sum of modules
  - - Note: ⨁ i, A i for A i modules is a module.
  - Prove (construct) that if Vᵢ are submodules of V that
    V ≃ ⊕ᵢ Vᵢ as bilinear form spaces if ⊕ᵢ Bᵢ is a basis for V given
    bases Bᵢ for Vᵢ
  - Prove that `is_orthog_direct_sum` B W₁ W₂ iff V ≃ W₁ ⊕ W₂ as bilinear form spaces
    (using the index function
      def foo (W₁ W₂: Submodule k V): Fin 2 → (Submodule k V)
      | 0 => W₁
      | 1 => W₂
    )

  Major Results (Planned - Aspirational)
  - State a version of the bases theorem but instead of commuting w/ bilinear form,
    a condition on the corresponding matrices of bilinear form being equal
-/

open LinearMap (BilinForm)
open LinearMap.BilinForm

namespace BilinIsomorphisms

variable {k V V' V'': Type*} [Field k] [AddCommGroup V] [AddCommGroup V'] [AddCommGroup V'']
  [Module k V] [Module k V'] [Module k V'']

@[ext]
structure EquivBilin (β: BilinForm k V) (β': BilinForm k V') where
  equiv : V ≃ₗ[k] V'
  comm_form : ∀v w, β v w = β' (equiv v) (equiv w)

/-
Include definitions for symm refl trans ...

Also maybe include proper instances for typeclasses?
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Logic/Equiv/Defs.html#Equiv.equiv_subsingleton_dom
-/

instance (β: BilinForm k V) (β': BilinForm k V'): EquivLike (EquivBilin β β') V V' where
  coe := fun a => a.equiv.toFun
  inv := fun a => a.equiv.invFun
  left_inv := fun a => a.equiv.left_inv
  right_inv := fun a => a.equiv.right_inv
  coe_injective' := fun _ _ h _ => by
    apply EquivBilin.ext
    exact LinearEquiv.ext_iff.mpr (congrFun h)

example (β: BilinForm k V) (β': BilinForm k V') (a: EquivBilin β β')
  (v w : V): a v = a w ↔ v=w := by exact EmbeddingLike.apply_eq_iff_eq a


def EquivBilin_of_basis_equiv {I I': Type*} {b: Basis I k V}
  {b': Basis I' k V'} {B: BilinForm k V} {B': BilinForm k V'} (hI: I ≃ I')
  (hB: ∀i j, B (b i) (b j) = B' (b' (hI i)) (b' (hI j)) ) : EquivBilin B B' where
  equiv := b.equiv b' hI
  comm_form := by
    let C : BilinForm k V := by
      apply LinearMap.mk₂' k k (fun v w => (B' ((b.equiv b' hI) v)) ((b.equiv b' hI) w))
      repeat simp_all
    have (v w: V):(B' ((b.equiv b' hI) v)) ((b.equiv b' hI) w)= C v w := by
      rfl
    simp_rw[this]
    suffices B = C from ?_
    . exact fun _ _ => by rw[this]
    apply LinearMap.BilinForm.ext_basis b
    intro i j
    unfold C
    simp only [hB, LinearMap.mk₂'_apply, Basis.equiv_apply]

-- Better name?
theorem EquivBilin_of_basis_equiv_align {I I': Type*} {b: Basis I k V}
  {b': Basis I' k V'} {B: BilinForm k V} {B': BilinForm k V'} (hI: I ≃ I')
  (hB: ∀i j, B (b i) (b j) = B' (b' (hI i)) (b' (hI j)) ) :
  ∀i, (EquivBilin_of_basis_equiv hI hB) (b i) = b' (hI i) := by
    intro i
    show (b.equiv b' hI) (b i) = b' (hI i)
    simp


end BilinIsomorphisms
