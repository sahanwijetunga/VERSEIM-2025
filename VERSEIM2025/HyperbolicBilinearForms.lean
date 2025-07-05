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

  TODO: **Define (and prove results for) Hyperbolic Space** (and prove an equivalence between
    inductive and non-inductive version)
    - Basis definition (e₁, ..., eₙ, f₁, ..., fₙ )
      - Basis → Inductive: If W₁ and W₂ are hyperbolic and
          is_orthog_direct_sum β W₁ W₂
        then V is also hyperbolic *Definition created, not proved*
      - Inductive → Basis: If V is hyperbolic then it can be constructed a direct sum
          of 2-dimensional hyperbolic spaces. *Theorem statement not created*

  TODO (LATER): Make definitions computable
-/

namespace Hyperbolic

variable {k V: Type*} [AddCommGroup V][Field k][Module k V]

open LinearMap (BilinForm)
open LinearMap.BilinForm
open BilinearForms -- This is the namespace in VERSEIM2025.Sahan.BilinearForms

@[simp]
abbrev isotropic (B: BilinForm k V) (e: V) := B e e = 0

-- left for e, right for f
-- Note: I am using a generic I: Type* instead of Fin n to make dealing with direct sums
--  easier
@[ext]
structure hypspace_fun_pred {I: Type*} (B: BilinForm k V) (b: I ⊕ I → V) where
  isotropic_left : ∀ i j, B (b (Sum.inl i)) (b (Sum.inl j)) = 0  -- B eᵢ eⱼ = 0 ∀ i j
  isotropic_right : ∀ i j, B (b (Sum.inr i)) (b (Sum.inr j)) = 0 -- B fᵢ fⱼ = 0 ∀ i j
  orthog1: ∀ i, ∀ j, (i ≠ j) → B (b (Sum.inl i)) (b (Sum.inr j)) = 0 -- B eᵢ fⱼ = 0 for i ≠ j
  orthog2: ∀ i, ∀ j, (i ≠ j) → B (b (Sum.inr i)) (b (Sum.inl j)) = 0 -- B fᵢ eⱼ = 0 for i ≠ j
  unital_corr: ∀ i, B (b (Sum.inl i)) (b (Sum.inr i)) = 1 -- B eᵢ fᵢ = 1 ∀ i


def hypspace_pred (B: BilinForm k V): Prop
  := ∃(I: Type*), ∃ (b: Basis (I ⊕ I)  k V), hypspace_fun_pred B b

@[ext]
structure hypspace (B: BilinForm k V) (I: Type*) where
  basis : Basis (I ⊕ I) k V
  pred: hypspace_fun_pred B basis

@[ext]
structure hypsubspace (B: BilinForm k V) (I: Type*) where
  coe : I ⊕ I → V
  linind : LinearIndependent k coe
  pred: hypspace_fun_pred B coe

@[simp]
def hypsubspace.toSubmodule {I: Type*} {B: BilinForm k V} (H : hypsubspace B I) : Submodule k V :=
  Submodule.span k (Set.range H.coe)

@[simp]
theorem hypspace_isotropic_left {B: BilinForm k V} {I: Type*} (H: hypspace B I) (i j: I):
  B (H.basis (Sum.inl i)) (H.basis (Sum.inl j))=0 := H.pred.isotropic_left i j

@[simp]
theorem hypspace_isotropic_right {B: BilinForm k V} {I: Type*} (H: hypspace B I) (i j: I):
  B (H.basis (Sum.inr i)) (H.basis (Sum.inr j))=0 := H.pred.isotropic_right i j

@[simp]
theorem hypspace_orthog1 {B: BilinForm k V} {I: Type*} (H: hypspace B I) (i j: I) (h: i ≠ j):
  B (H.basis (Sum.inl i)) (H.basis (Sum.inr j)) = 0 := H.pred.orthog1 i j h

@[simp]
theorem hypspace_orthog2 {B: BilinForm k V} {I: Type*} (H: hypspace B I) (i j: I) (h: i ≠ j):
  B (H.basis (Sum.inr i)) (H.basis (Sum.inl j)) = 0 := H.pred.orthog2 i j h

@[simp]
theorem hypspace_unital_corr {B: BilinForm k V} {I: Type*} (H: hypspace B I) (i: I):
  B (H.basis (Sum.inl i)) (H.basis (Sum.inr i)) = 1 := H.pred.unital_corr i


-- Sahan: I would prefer to have the submodule inferred but I can't figure out how to
-- noncomputable instance {I: Type*} (B: BilinForm k V) : Coe (hypsubspace B I) (Submodule k V) where
--   coe := hypsubspace.toSubmodule

-- Sahan: I ran into difficulties with creating objects; Ideally figure out how to delete the protected below defns.
protected def Basis_repr_left{B: BilinForm k V} {I: Type*} (H: hypspace B I) (i: I):
  V →ₗ[k] k where
  toFun := fun v ↦ (H.basis.repr v) (Sum.inl i)
  map_add' := by simp
  map_smul' := by simp

protected noncomputable def Basis_form_right {B: BilinForm k V} {I: Type*} (H: hypspace B I) (i: I):
  V →ₗ[k] k where
  toFun := fun v ↦ B v (H.basis (Sum.inr i))
  map_add' := by simp
  map_smul' := by simp

protected theorem Basis_repr_left_eq_Basis_form_right {B: BilinForm k V} {I: Type*} (H: hypspace B I) (i: I):
  Hyperbolic.Basis_repr_left H i = Hyperbolic.Basis_form_right H i := by
    apply  Basis.ext H.basis
    intro j
    match j with
    | Sum.inl j =>
      dsimp[Hyperbolic.Basis_repr_left,Hyperbolic.Basis_form_right]
      by_cases h:i = j
      . simp[h]
      . have: j ≠ i := by exact fun a ↦ h (id (Eq.symm a))
        simp_all
    | Sum.inr j =>
      dsimp[Hyperbolic.Basis_repr_left,Hyperbolic.Basis_form_right]
      by_cases h:i = j
      . simp[h]
      . simp_all

theorem hypspace_repr_left {B: BilinForm k V} {I: Type*} (H: hypspace B I) (v: V) (i: I):
  (H.basis.repr v) (Sum.inl i) = B v (H.basis (Sum.inr i)) := by
    have hleft: (H.basis.repr v) (Sum.inl i) = Hyperbolic.Basis_repr_left H i v := by
      simp[Hyperbolic.Basis_repr_left]
    have hright: B v (H.basis (Sum.inr i)) = Hyperbolic.Basis_form_right H i v:= by
      simp[Hyperbolic.Basis_form_right]
    rw[hleft, hright]
    rw[Hyperbolic.Basis_repr_left_eq_Basis_form_right H i]

-- Proving this should be similar to the prior theorem
theorem hypspace_repr_right {B: BilinForm k V} {I: Type*} (H: hypspace B I) (v: V) (i: I):
  (H.basis.repr v) (Sum.inr i) = B (H.basis (Sum.inl i)) v  := sorry

noncomputable def hypsubspace.tohypspace {B: BilinForm k V} {I: Type*} (H: hypsubspace B I):
  hypspace (B.restrict H.toSubmodule) I where
  basis := by  sorry
  pred := sorry

noncomputable def hypsubspace.tohypspace' {B: BilinForm k V} {I: Type*} (H: hypsubspace B I)
  (hspan: H.toSubmodule= ⊤): hypspace B I where
  basis := by  sorry -- apply @Basis.mk
  pred := sorry

-- TODO: Move definition to VERSEIM2025/Sahan.BilinearForms.lean
structure is_orthog_ind (B: BilinForm k V) (W₁: Submodule k V) (W₂: Submodule k V) where
  ind: W₁ ⊓ W₂ = ⊥
  orthog: OrthogSubspaces B W₁ W₂

noncomputable def hypsubspace_of_orthog_ind {B: BilinForm k V} {I J: Type*} {H₁: hypsubspace B I}
  {H₂: hypsubspace B J} (h: is_orthog_ind B H₁.toSubmodule  H₂.toSubmodule):
  hypsubspace B (I ⊕ J) := sorry

theorem hypsubspace_of_direct_sum_hypsubspaces (B: BilinForm k V) (I J: Type*)
  (H₁: hypsubspace B I) (H₂: hypsubspace B J) (h: is_orthog_ind B H₁.toSubmodule
  H₂.toSubmodule): (hypsubspace_of_orthog_ind h).toSubmodule = H₁.toSubmodule ⊔ H₂.toSubmodule := by
    sorry

noncomputable def hypspace_of_orthog_direct_sum (B: BilinForm k V) (I J: Type*) (H₁: hypsubspace B I)
  (H₂: hypsubspace B J) (h: is_orthog_direct_sum B H₁.toSubmodule  H₂.toSubmodule):
  hypspace B (I ⊕ J) := sorry

def hyp_pair (β:BilinForm k V) (e f : V) : Prop :=
  β e e = 0  ∧  β f f = 0  ∧  β e f = 1

-- TODO: Move to another file (and prove) or find appropriate mathlib lemma
theorem SumLinearIndependent {I J: Type*} {v: I → V} {w: J → V} (hv: LinearIndependent k v)
  (hw: LinearIndependent k w) (hvw: Submodule.span k (Set.range v) ⊓ Submodule.span k (Set.range w)=⊥):
   LinearIndependent k (Sum.elim v w) := sorry

abbrev singleton := Fin 1

-- This should reduce down to 0 ≠ 1 in k
lemma hyp_pair_nonzero {β: BilinForm k V} {e f: V} (h: hyp_pair β e f) : e ≠ 0 ∧ f ≠ 0 := by
  sorry

lemma LinearIndependent_of_fun_singleton_nonzero {v: V} (h: v≠ 0):
  LinearIndependent k (fun (a: singleton) ↦ v) := sorry

def hypsubspace_two {B: BilinForm k V} {e f: V} (h: hyp_pair B e f): hypsubspace B singleton
   where
   coe := Sum.elim (fun _ ↦ e) (fun _ ↦ f)
   linind := by
      have ⟨he, hf⟩ := hyp_pair_nonzero h
      have heInd: LinearIndependent k (fun (a: singleton) ↦ e) := by
        exact LinearIndependent_of_fun_singleton_nonzero he
      have hfInd: LinearIndependent k (fun (a: singleton) ↦ f) := by
        exact LinearIndependent_of_fun_singleton_nonzero hf
      apply SumLinearIndependent heInd hfInd
      simp_all
      suffices Submodule.span k {e} ⊓ Submodule.span k {f} ≤ ⊥ from ?_
      . apply (Submodule.eq_bot_iff (Submodule.span k {e} ⊓ Submodule.span k {f})).mpr this
      rintro a ⟨hae, haf⟩
      show a=0
      have hae: ∃(c: k), c • e= a := by
        exact Submodule.mem_span_singleton.mp hae
      have haf: ∃(d: k), d • f= a := by
        exact Submodule.mem_span_singleton.mp haf
      have ⟨c, hc⟩ := hae
      have ⟨d, hd⟩ := haf
      have h': B e f = 1 := h.right.right
      contrapose! h'
      suffices B e f = 0 from ?_
      . rw[this]
        exact Ne.symm one_ne_zero
      have hec: e = c⁻¹ • a := by
        have: c ≠ 0 := by
          intro h
          rw[h, zero_smul] at hc
          exact h' hc.symm
        rw[<- hc,smul_smul,inv_mul_cancel₀ this]
        module
      rw[hec, <- hd]
      simp[h.right.left]
   pred := by sorry

-- Sahan: Better name?
def foo_equiv (I: Type*): I ⊕ I ≃ I × (singleton ⊕ singleton) where
  toFun
  | Sum.inl i => (i,Sum.inl 0)
  | Sum.inr i => (i,Sum.inr 0)
  invFun
  | (i,Sum.inl 0) => Sum.inl i
  | (i,Sum.inr 0) => Sum.inr i
  left_inv
  | Sum.inl i => by simp
  | Sum.inr i => by simp
  right_inv
  | (i,Sum.inl 0) => by simp
  | (i,Sum.inr 0) => by simp

/- TODO: Prove that a hyspace is a direct sum of hypsubspace_two's

  This should be formulated in the sense of isomorphism of bilinear forms. This
  requires things in BilinearFormIsomorphisms not yet created. Make use of
  (planned) theorem reducing to proving basis equivalence.
-/

theorem hypspace.Nondegenerate{I: Type*}  {B:BilinForm k V}
  (H: hypspace B I) (brefl : IsRefl B) :
  Nondegenerate B := by
    intro v hv
    let b := H.basis
    have hleft: ∀ i, (b.repr v) (Sum.inl i) = 0 := by
      intro i
      rw[hypspace_repr_left H v i]
      exact hv _
    have hright: ∀ i, (b.repr v) (Sum.inr i) = 0 := by
      intro i
      rw[hypspace_repr_right H v i]
      rw[brefl] -- Note: If we assumed finite dimensionality we could instead use nondeg_conditions
      exact hv _
    have h: ∀ i, (b.repr v) i = 0
    |  Sum.inl i => hleft i
    |  Sum.inr i => hright i
    exact (Basis.forall_coord_eq_zero_iff b).mp h

-- TODO: Move to a better file location
theorem IsRefl_restrict {B: BilinForm k V} (brefl: IsRefl B) (W: Submodule k V):
  IsRefl (B.restrict W) := fun x y ↦ brefl (W.subtype x) (W.subtype y)

theorem hypsubspace.NondegenerateOn {B:BilinForm k V}
  (brefl : IsRefl B) {I: Type*} (H: hypsubspace B I) :
  NondegenerateOn B H.toSubmodule := by
    exact H.tohypspace.Nondegenerate (IsRefl_restrict brefl H.toSubmodule)


theorem hyp2_nondeg_refl (β:BilinForm k V)
  (brefl : IsRefl β) {e f : V} (h2: hyp_pair β e f) :
  NondegenerateOn β (hypsubspace_two h2).toSubmodule := by
    exact (hypsubspace_two h2).NondegenerateOn brefl


theorem hyp2_nondeg_symm (β:BilinForm k V)
  (bsymm : IsSymm β) {e f : V} (h2: hyp_pair β e f) :
  NondegenerateOn β (hypsubspace_two h2).toSubmodule  := by
  have brefl: IsRefl β := IsSymm.isRefl bsymm
  exact hyp2_nondeg_refl β brefl h2

theorem hyp2_nondeg_alt (β:BilinForm k V)
  (balt : IsAlt β) {e f : V} (h2: hyp_pair β e f) :
  NondegenerateOn β (hypsubspace_two h2).toSubmodule  := by
  have brefl: IsRefl β := IsAlt.isRefl balt
  exact hyp2_nondeg_refl β brefl h2

-- using `orthog_decomp` from BilinearForms, we get

def hyp2_decomp_symm (β:BilinForm k V) [FiniteDimensional k V] (bsymm : IsSymm β) (e f : V) (h2:hyp_pair β e f)
  : orthog_direct_sum β (hypsubspace_two h2).toSubmodule :=
  orthog_decomp β (hypsubspace_two h2).toSubmodule (hyp2_nondeg_symm  β bsymm h2)

def hyp2_decomp_alt (β:BilinForm k V) [FiniteDimensional k V] (balt : IsAlt β) (e f : V) (h2:hyp_pair β e f)
  : orthog_direct_sum β (hypsubspace_two h2).toSubmodule :=
  orthog_decomp β (hypsubspace_two h2).toSubmodule (hyp2_nondeg_alt  β balt h2)


lemma exists_bilin_one {e: V} {B: BilinForm k V} (enz: e ≠ 0)
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


theorem hyp_pair_exists_symm {e: V} (p: ℕ) {β:BilinForm k V} (bsymm : IsSymm β) (hn: Nondegenerate β) (enz : e ≠ 0)
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


theorem hyp_pair_exists_alt {e: V} {β:BilinForm k V} (balt : IsAlt β) (hn: Nondegenerate β) (enz : e ≠ 0) :
  ∃ f, hyp_pair β e f := by
    have ⟨v, hv⟩ := exists_bilin_one enz hn
    use v
    constructor; . exact balt e
    constructor
    . exact balt v
    . exact hv



end Hyperbolic
