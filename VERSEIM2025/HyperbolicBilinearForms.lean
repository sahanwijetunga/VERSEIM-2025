--------------------------------------------------------------------------------
/-
Copyright (c) 2025 Clea Bergsman, Katherine Buesing, George McNinch, Sahan Wijetunga. All rights reserved.

Released under the Apache 2.0 license as described in the file LICENSE.

VERSEIM-2025 REU @ Tufts University
-/

import Mathlib.Tactic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import VERSEIM2025.Sahan.BilinearForms

/- Sahan: This file is to state definitions for hyperbolic forms,
  and prove theorems proving various equivalences.

  Proofs that other forms (say symmetric, alternating, nondegenerate) are
  hyperbolic should be included in other files.

  Note: There will likely be some differences between definitions/theorems here and in
  BilinearForms
    - For now, statements are imported from VERSEIM2025.Sahan.BilinearForms
      as all statements about hyperbolic forms were removed from there.
    - We should probably make the files correspond and change the import to
      VERSEIM2025.BilinearForms at some point.

  TODO: **Define Hyperbolic Space** (and prove an equivalence between
    inductive and non-inductive version)
    - Basis definition (e₁, ..., eₙ, f₁, ..., fₙ )
      - Basis → Inductive: If W₁ and W₂ are hyperbolic and
          is_orthog_direct_sum β W₁ W₂
        then V is also hybolic
      - Inductive → Basis: If V is hyperbolic then it can be constructed a direct sum
          of 2-dimensional hyperbolic spaces.
-/

namespace Hyperbolic

variable {k V: Type*} [AddCommGroup V][Field k][Module k V]

open LinearMap (BilinForm)
open LinearMap.BilinForm
open BilinearForms -- This is the namespace in VERSEIM2025.Sahan.BilinearForms

abbrev isotropic (B: BilinForm k V) (e: V) := B e e = 0

-- left for e, right for f
structure hypspace_basis_pred (B: BilinForm k V) (b: Basis (Fin n ⊕ Fin n) k V) where
  isotropic_left : ∀ i, isotropic B (b (Sum.inl i)) -- B eᵢ eᵢ = 0 ∀ i
  isotropic_right : ∀ i, isotropic B (b (Sum.inr i)) -- B fᵢ fᵢ = 0 ∀ i
  orthog1: ∀ i, ∀ j, (i ≠ j) → B (b (Sum.inl i)) (b (Sum.inr j)) = 0 -- B eᵢ fⱼ = 0 for i ≠ j
  orthog2: ∀ i, ∀ j, (i ≠ j) → B (b (Sum.inr i)) (b (Sum.inl j)) = 0 -- B fᵢ eⱼ = 0 for i ≠ j
  unital_corr: ∀ i, B (b (Sum.inl i)) (b (Sum.inr i)) = 1 -- B eᵢ fᵢ = 1 ∀ i

def hypspace_pred (B: BilinForm k V): Prop
  := ∃(n: ℕ), ∃ (b: Basis ((Fin n) ⊕ (Fin n))  k V), hypspace_basis_pred B b

-- Change to structure
def hypsubspace (W: Submodule k V): True := sorry


/- Add in rest of definitions for hypersubspaces-/

def hyp_pair (β:BilinForm k V) (e f : V) : Prop :=
  β e e = 0  ∧  β f f = 0  ∧  β e f = 1

def hypsubspace_two {β:BilinForm k V} {e f : V} (_:hyp_pair β e f) : Submodule k V :=
  Submodule.span k {e,f}

lemma in_span_fin_iff_linear_combination (n: ℕ) (v: V) (vect: Fin n → V) (hv : v ∈ Submodule.span k (Set.range vect)) :
  ∃(f: Fin n → k), v = ∑ i, f i • (vect i) := by
    rw[Submodule.mem_span_range_iff_exists_fun] at hv
    have ⟨c, hc⟩ := hv
    use c
    symm
    exact hc

lemma in_span_fin_two_iff_linear_combination (v: V) (vect: Fin 2 → V) (hv : v ∈ Submodule.span k (Set.range vect)) :
  ∃(f: Fin 2 → k), v = ∑ i, f i • (vect i) := by
    exact in_span_fin_iff_linear_combination (2: ℕ) (v: V) (vect: Fin 2 → V) hv

def fun_fin_two_to_pair (e f : V) : Fin 2 → V
| ⟨0, _⟩ => e
| ⟨1, _⟩ => f

lemma exists_two_coefficients_of_in_span_pair (v1 v2 v : V)(hv : v ∈ Submodule.span k {v1, v2}) :
  ∃(a b: k), v = a • v1 + b • v2 := by
    have: {v1, v2} = Set.range (fun_fin_two_to_pair v1 v2):= by
      ext x
      constructor
      . rintro (h | h)
        . use 0; simp only [fun_fin_two_to_pair]; tauto
        . use 1; simp only [fun_fin_two_to_pair]; symm; exact h
      . rintro ⟨y, rfl⟩
        match y with
        | ⟨0, _⟩ => simp[fun_fin_two_to_pair]
        | ⟨1, _⟩ => simp[fun_fin_two_to_pair]
    rw[this] at hv
    have ⟨f, hv⟩ := in_span_fin_two_iff_linear_combination v (fun_fin_two_to_pair v1 v2) hv
    use f 0, f 1
    rw[hv]
    exact Fin.sum_univ_two fun i ↦ f i • fun_fin_two_to_pair v1 v2 i

theorem hyp2_nondeg_refl (β:BilinForm k V)
  (brefl : IsRefl β) {e f : V} (h2: hyp_pair β e f) :
  NondegenerateOn β (hypsubspace_two h2) := by
    rintro ⟨v, hv⟩  h
    have: ∃(a b: k), v = a • e + b • f := by
      unfold hypsubspace_two at hv
      exact exists_two_coefficients_of_in_span_pair e f v hv
    have ⟨a,b,hab⟩ := this
    have hve: β v e = 0 := by
      have he: e ∈ hypsubspace_two h2 := by
        simp[hypsubspace_two]
        suffices e ∈ ({e,f} : Set V)from ?_
        . exact Submodule.mem_span_of_mem this
        exact Set.mem_insert e {f}
      apply h ⟨e, he⟩

    have hvf: β v f = 0 := by
      have hf: f ∈ hypsubspace_two h2 := by
        simp[hypsubspace_two]
        suffices f ∈ ({e,f} : Set V)from ?_
        . exact Submodule.mem_span_of_mem this
        exact Set.mem_insert_of_mem e rfl
      apply h ⟨f, hf⟩

    have hveb: β e v = b := by
      calc
        β e v = β e (a• e + b • f) := by rw[hab]
        _ = a * β e e + b * β e f := by simp
        _ = a * 0 + b * 1 := by
          unfold hyp_pair at h2
          have: β e e = 0 := by
            exact h2.left
          have: β e f= 1 := by
            exact h2.right.right
          simp[*]
        _ =  b := by simp
    have hvfa: β v f = a:= by
        calc
        β v f = β (a• e + b • f) f := by rw[hab]
        _ = a * β e f + b * β f f := by simp
        _ = a * 1 + b * 0 := by
          unfold hyp_pair at h2
          have: β e f = 1 := by
            exact h2.right.right
          have: β f f = 0 := by
            exact h2.right.left
          simp[*]
        _ = a := by simp
    have hva: a=0 :=
      calc
        a= β v f := hvfa.symm
        _ = 0 := hvf
    have hvb: b=0 := by
      have hve': β e v = 0 := brefl v e hve
      calc
        b = β e v:= hveb.symm
        _ = 0 := hve'

    simp[hab,hva,hvb]

theorem hyp2_nondeg_symm (β:BilinForm k V)
  (bsymm : IsSymm β) {e f : V} (h2: hyp_pair β e f) :
  NondegenerateOn β (hypsubspace_two h2)  := by
  have brefl: IsRefl β := IsSymm.isRefl bsymm
  exact hyp2_nondeg_refl β brefl h2

theorem hyp2_nondeg_alt (β:BilinForm k V)
  (balt : IsAlt β) {e f : V} (h2: hyp_pair β e f) :
  NondegenerateOn β (hypsubspace_two h2)  := by
  have brefl: IsRefl β := IsAlt.isRefl balt
  exact hyp2_nondeg_refl β brefl h2


-- using `orthog_decomp` from BilinearForms, we get

def hyp2_decomp_symm (β:BilinForm k V) [FiniteDimensional k V] (bsymm : IsSymm β) (e f : V) (h2:hyp_pair β e f)
  : orthog_direct_sum β (hypsubspace_two h2) :=
  orthog_decomp β (hypsubspace_two h2) (hyp2_nondeg_symm  β bsymm h2)

def hyp2_decomp_alt (β:BilinForm k V) [FiniteDimensional k V] (balt : IsAlt β) (e f : V) (h2:hyp_pair β e f)
  : orthog_direct_sum β (hypsubspace_two h2) :=
  orthog_decomp β (hypsubspace_two h2) (hyp2_nondeg_alt  β balt h2)


lemma exists_bilin_one {B: BilinForm k V} (enz: e ≠ 0)
  (hn: Nondegenerate B): ∃f, B e f =1 := by
    have: ∃ f, B e f ≠ 0 := by
      contrapose! enz
      exact hn e enz
    have ⟨f, hf⟩ := this
    let a := B e f
    use a⁻¹ • f
    calc
      (B e) (a⁻¹ • f) = a⁻¹ * (B e f) := by simp only [map_smul, smul_eq_mul]
      _ = a⁻¹ * a := rfl
      _ = 1 := inv_mul_cancel₀ hf


theorem hyp_pair_exists_symm {β:BilinForm k V} (bsymm : IsSymm β) (hn: Nondegenerate β) (enz : e ≠ 0)
  (eiso : β e e  = 0) [CharP k p] (hn2 : p ≠ 2):
  ∃ f, hyp_pair β e f := by
    have ⟨v, hv⟩ := exists_bilin_one enz hn
    let c := - 2⁻¹ * β v v
    let v' := v+c • e
    use v'
    constructor
    . exact eiso
    constructor
    . unfold v' c
      have : β v e = 1 := by
        rw[<- bsymm]
        exact hv
      have: (2: k) ≠ 0 := by
        apply Ring.two_ne_zero
        rw [ ringChar.eq k p ]
        exact hn2
      field_simp[*]
      ring
    . unfold v' c
      simp_all


theorem hyp_pair_exists_alt {β:BilinForm k V} (balt : IsAlt β) (hn: Nondegenerate β) (enz : e ≠ 0) :
  ∃ f, hyp_pair β e f := by
    have ⟨v, hv⟩ := exists_bilin_one enz hn
    use v
    constructor; . exact balt e
    constructor
    . exact balt v
    . exact hv

end Hyperbolic
