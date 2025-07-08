--------------------------------------------------------------------------------
/-
Copyright (c) 2025 Clea Bergsman, Katherine Buesing, George McNinch, Sahan Wijetunga. All rights reserved.

Released under the Apache 2.0 license as described in the file LICENSE.

VERSEIM-2025 REU @ Tufts University
-/

import VERSEIM2025.BilinearFormIsomorphisms


/-
  This file is to state definitions for hyperbolic forms,
  and prove theorems proving various equivalences.

  Proofs that other forms (say symmetric, alternating, nondegenerate) are
  hyperbolic should be included in other files.

  Note: There will likely be some differences between definitions/theorems here and in
  BilinearForms
    - For now, statements are imported from VERSEIM2025.Sahan.BilinearForms
      as all statements about hyperbolic forms were removed from there.
    - We should probably make the files correspond and change the import to
      VERSEIM2025.BilinearForms at some point.

  Note: Everything is Type not Type* due to issues with existence statements
  - As a result, anything relying on the results here must be Type not Type*

  TODO: **Define (and prove results for) Hyperbolic Space** (and prove an equivalence between
    inductive and non-inductive version)
    - Basis definition (e₁, ..., eₙ, f₁, ..., fₙ )
      - Basis → Inductive: If W₁ and W₂ are hyperbolic and
          is_orthog_direct_sum β W₁ W₂
        then V is also hyperbolic *Definition created, not proved*
      - Inductive → Basis: If V is hyperbolic then it can be constructed a direct sum
          of 2-dimensional hyperbolic spaces. *Theorem created, not proved*

  TODO (LATER): Make definitions computable
-/

namespace Hyperbolic

variable {k V: Type} [AddCommGroup V][Field k][Module k V]

open LinearMap (BilinForm)
open LinearMap.BilinForm
open BilinearForms -- This is the namespace in VERSEIM2025.Sahan.BilinearForms
open BilinIsomorphisms -- This is the namespace in VERSEIM2025.BilinearFormIsomorphisms

@[simp]
abbrev isotropic (B: BilinForm k V) (e: V) := B e e = 0

/-- left for *e*, right for *f*, i.e.
      eᵢ = Sum.inl i
      fᵢ = Sum.inr i
    Essentially each Span (eᵢ, fᵢ) is a hyperbolic 2-space and the span of b
      is a direct sum of these 2-spaces.
 -/
@[ext]
structure Hypspace_fun_pred {I: Type} (B: BilinForm k V) (b: I ⊕ I → V) where
  isotropic_left : ∀ i j, B (b (Sum.inl i)) (b (Sum.inl j)) = 0
  isotropic_right : ∀ i j, B (b (Sum.inr i)) (b (Sum.inr j)) = 0 -- B fᵢ fⱼ = 0 ∀ i j
  orthog1: ∀ i, ∀ j, (i ≠ j) → B (b (Sum.inl i)) (b (Sum.inr j)) = 0 -- B eᵢ fⱼ = 0 for i ≠ j
  orthog2: ∀ i, ∀ j, (i ≠ j) → B (b (Sum.inr i)) (b (Sum.inl j)) = 0 -- B fᵢ eⱼ = 0 for i ≠ j
  unital_corr: ∀ i, B (b (Sum.inl i)) (b (Sum.inr i)) = 1 -- B eᵢ fᵢ = 1 ∀ i

/-- There exists a basis such that `Hypspace_fun_pred` holds. -/
def Hypspace_pred (B: BilinForm k V): Prop
  := ∃(I: Type), ∃ (b: Basis (I ⊕ I)  k V), Hypspace_fun_pred B b

/-- A Hyperbolic Space

  Contains a basis which satisfies `Hypspace_fun_pred`-/
@[ext]
structure Hypspace (B: BilinForm k V) where
  I: Type
  basis : Basis (I ⊕ I) k V
  pred: Hypspace_fun_pred B basis

/-- The zero vector space is Hyperbolic. -/
noncomputable def Hypspace_zero {B: BilinForm k V} (h: ∀ (v: V), v=0): Hypspace B where
  I := Empty
  basis := by
    have h': Module.rank k V =0 := rank_zero_iff_forall_zero.mpr h
    exact Basis.ofRankEqZero h'
  pred := {
    isotropic_left := fun i => by contradiction,
    isotropic_right := fun i => by contradiction,
    orthog1 := fun i => by contradiction,
    orthog2 := fun i => by contradiction,
    unital_corr := fun i => by contradiction }

/-- The basis index type `H.I ⊕ H.I` for `H: Hypspace`.

    Created to maintain standard with `OddHyperbolic` and `GeneralizedHyperbolic` in
    `OddHyperbolicForms.lean`-/
@[simp]
abbrev Hypspace.basis_index {B: BilinForm k V} (H: Hypspace B) := H.I ⊕ H.I

protected theorem Hypspace_of_Hypspace_pred_aux {B: BilinForm k V} (h: Hypspace_pred B): Nonempty (Hypspace B) := by
    have ⟨I, b, hbI⟩ := h
    constructor
    exact Hypspace.mk I b hbI

/-- Noncomputably yields a `Hypspace` from `Hypspace_pred`-/
noncomputable def Hypspace_of_Hypspace_pred {B: BilinForm k V} (h: Hypspace_pred B): Hypspace B := by
    apply Classical.choice
    have ⟨H⟩ := Hyperbolic.Hypspace_of_Hypspace_pred_aux h
    constructor
    exact H

/-- The Bilinear form associated to a `Hypspace` satisfies `Hypspace_pred`-/
theorem Hypspace_pred_of_Hypspace {B: BilinForm k V} (H: Hypspace B):
  Hypspace_pred B:= by
    use H.I
    use H.basis
    exact H.pred


@[ext]
structure Hypsubspace (B: BilinForm k V) where
  I: Type
  coe : I ⊕ I → V
  linind : LinearIndependent k coe
  pred: Hypspace_fun_pred B coe

example (W: Submodule k V) (f: I → W): I → V := fun i ↦ f i


@[simp]
abbrev Hypsubspace.basis_index {B: BilinForm k V} (H: Hypsubspace B) := H.I ⊕ H.I

@[simp]
def Hypsubspace.toSubmodule {B: BilinForm k V} (H : Hypsubspace B) : Submodule k V :=
  Submodule.span k (Set.range H.coe)

@[simp]
noncomputable def Hypsubspace.basis {B: BilinForm k V} (H : Hypsubspace B) : Basis H.basis_index k H.toSubmodule := by
  apply Basis.mk
  case v => exact (fun i => ⟨H.coe i, Submodule.mem_span_of_mem (Set.mem_range_self i)⟩ )
  case hli =>
    sorry
  case hsp =>
    sorry

def Hypsubspace_of_Hypspace_submodule {B: BilinForm k V} {W: Submodule k V}
 (H : Hypspace (B.restrict W)) : Hypsubspace B := sorry

def Hypsubspace_of_Hypspace_submodule_toSubmodule_agrees {B: BilinForm k V} {W: Submodule k V}
 (H : Hypspace (B.restrict W)) : (Hypsubspace_of_Hypspace_submodule H).toSubmodule = W := sorry


@[simp]
theorem Hypspace_isotropic_left {B: BilinForm k V} (H: Hypspace B) (i j: H.I):
  B (H.basis (Sum.inl i)) (H.basis (Sum.inl j))=0 := H.pred.isotropic_left i j

@[simp]
theorem Hypspace_isotropic_right {B: BilinForm k V} (H: Hypspace B) (i j: H.I):
  B (H.basis (Sum.inr i)) (H.basis (Sum.inr j))=0 := H.pred.isotropic_right i j

@[simp]
theorem Hypspace_orthog1 {B: BilinForm k V} (H: Hypspace B) (i j: H.I) (h: i ≠ j):
  B (H.basis (Sum.inl i)) (H.basis (Sum.inr j)) = 0 := H.pred.orthog1 i j h

@[simp]
theorem Hypspace_orthog2 {B: BilinForm k V} (H: Hypspace B) (i j: H.I) (h: i ≠ j):
  B (H.basis (Sum.inr i)) (H.basis (Sum.inl j)) = 0 := H.pred.orthog2 i j h

@[simp]
theorem Hypspace_unital_corr {B: BilinForm k V} (H: Hypspace B) (i: H.I):
  B (H.basis (Sum.inl i)) (H.basis (Sum.inr i)) = 1 := H.pred.unital_corr i


@[simp]
theorem Hypsubspace_isotropic_left {B: BilinForm k V} (H: Hypsubspace B) (i j: H.I):
  B (H.coe (Sum.inl i)) (H.coe (Sum.inl j))=0 := H.pred.isotropic_left i j

@[simp]
theorem Hypsubspace_isotropic_right {B: BilinForm k V}  (H: Hypsubspace B) (i j: H.I):
  B (H.coe (Sum.inr i)) (H.coe (Sum.inr j))=0 := H.pred.isotropic_right i j

@[simp]
theorem Hypsubspace_orthog1 {B: BilinForm k V} (H: Hypsubspace B) (i j: H.I) (h: i ≠ j):
  B (H.coe (Sum.inl i)) (H.coe (Sum.inr j)) = 0 := H.pred.orthog1 i j h

@[simp]
theorem Hypsubspace_orthog2 {B: BilinForm k V} (H: Hypsubspace B) (i j: H.I) (h: i ≠ j):
  B (H.coe (Sum.inr i)) (H.coe (Sum.inl j)) = 0 := H.pred.orthog2 i j h

@[simp]
theorem Hypsubspace_unital_corr {B: BilinForm k V} (H: Hypsubspace B) (i: H.I):
  B (H.coe (Sum.inl i)) (H.coe (Sum.inr i)) = 1 := H.pred.unital_corr i

theorem Hypsubspace_of_Hypspace_pred_restrict {B: BilinForm k V} {W: Submodule k V}
 (h: Hypspace_pred <| B.restrict W): ∃ (H: Hypsubspace B), H.toSubmodule = W := by
    let H' := Hypspace_of_Hypspace_pred h
    use Hypsubspace_of_Hypspace_submodule H'
    exact Hypsubspace_of_Hypspace_submodule_toSubmodule_agrees H'

@[simp]
noncomputable def Hypsubspace.toHypspace {B: BilinForm k V} (H: Hypsubspace B):
  Hypspace (B.restrict H.toSubmodule) where
  I := H.I
  basis := H.basis
  pred := sorry

theorem Hypsubspace_basis_compatible {B: BilinForm k V} (H: Hypsubspace B):
  H.toHypspace.basis = H.basis := rfl

noncomputable def Hypsubspace.toHypspace' {B: BilinForm k V} (H: Hypsubspace B)
  (hspan: H.toSubmodule= ⊤): Hypspace B where
  I := H.I
  basis := by  sorry -- apply @Basis.mk
  pred := sorry


@[simp]
abbrev sum_iso {I I': Type} (π: I ≃ I') : I ⊕ I ≃ I' ⊕ I' := π.sumCongr π

noncomputable def Hypspace.iso_from_iso_index {V': Type} {B: BilinForm k V} [AddCommGroup V']
  [Module k V'] {B': BilinForm k V'} (H: Hypspace B) (H': Hypspace B') (π: H.I ≃ H'.I)
  (h: ∀ i, B (H.basis <| Sum.inr i) (H.basis <| Sum.inl i) = B' (H'.basis <| Sum.inr <| π i) (H'.basis <| Sum.inl <| π i) ) :
  EquivBilin B B' := by
    have (i: H.basis_index) (j: H.basis_index):  B (H.basis i) (H.basis j) = B' (H'.basis <| sum_iso π i) (H'.basis <| sum_iso π j) :=
      match i with
      | Sum.inl i => match j with
        | Sum.inl j => by simp_all
        | Sum.inr j => by
          by_cases h':(i = j)
          . simp[h']
          . simp[h']
      | Sum.inr i =>  match j with
        | Sum.inl j => by
          by_cases h':(i = j)
          . simp[h',h]
          . simp[h']
        | Sum.inr j => by simp_all
    exact EquivBilin_of_basis_equiv (sum_iso π) this

theorem Hypspace_rank {B: BilinForm k V} (H: Hypspace B):
  Module.rank k V=2*Cardinal.mk H.I := by
  have: 2*Cardinal.mk H.I = Cardinal.mk (H.I ⊕ H.I ) := by
    have: Cardinal.mk H.I + Cardinal.mk H.I = 2*Cardinal.mk H.I := by
      exact Eq.symm (two_mul (Cardinal.mk H.I))
    rw[<- this]
    rfl
  rw[this]
  exact Eq.symm (Basis.mk_eq_rank'' H.basis)

theorem Hypspace_finrank {B: BilinForm k V} (H: Hypspace B) [Fintype H.I] :
  Module.finrank k V=2*Fintype.card H.I := by
  have: 2*Fintype.card H.I = Fintype.card (H.I ⊕ H.I ) := by
    have: Fintype.card H.I + Fintype.card H.I = 2*Fintype.card H.I := by
      exact Eq.symm (Nat.two_mul (Fintype.card H.I))
    rw[<- this]
    exact Eq.symm Fintype.card_sum
  rw[this]
  exact Module.finrank_eq_card_basis H.basis

theorem Hypspace_finrank_Fin_n {n: ℕ} {B: BilinForm k V} (H: Hypspace B) (h: H.I=Fin n):
  Module.finrank k V=2*n := by
  have : Fintype H.I := by
    suffices Finite H.I from by exact Fintype.ofFinite H.I
    rw[h]
    exact Finite.of_fintype (Fin n)
  rw[Hypspace_finrank H]
  have: Fintype.card H.I = n := by
    rw[<- Fintype.card_fin n]
    exact Fintype.card_congr' h
  rw[this]

noncomputable instance {B: BilinForm k V}[FiniteDimensional k V] (H: Hypspace B): Fintype H.I := by
    have: Finite H.I := by
      refine @Finite.sum_left H.I H.I ?_
      have := H.basis
      refine Fintype.finite ?_
      exact FiniteDimensional.fintypeBasisIndex this
    exact Fintype.ofFinite H.I

-- Note: I would prefer to make this an instance but lean doesn't accept it
def Hypspace.FiniteDimensionalVS {B: BilinForm k V} (H: Hypspace B) [Fintype H.I] : (FiniteDimensional k V) := by
  suffices Finite (H.basis_index) from Module.Finite.of_basis H.basis
  infer_instance

instance  {B: BilinForm k V} (H: Hypsubspace B) [Fintype H.I]: Fintype H.toHypspace.I :=
  have: Fintype H.I := inferInstance
  this

instance Hypsubspace.FiniteDimensionalVS {B: BilinForm k V} (H: Hypsubspace B) [Fintype H.I] : (FiniteDimensional k H.toSubmodule) := by
  exact Hypspace.FiniteDimensionalVS H.toHypspace

noncomputable instance {B: BilinForm k V}[FiniteDimensional k V] (H: Hypsubspace B):
  Fintype H.toHypspace.I := inferInstance

theorem Hypspace.is_even_dimension {B: BilinForm k V}  [FiniteDimensional k V] (H: Hypspace B):
  Even (Module.finrank k V) := sorry

-- This should be provable without finiteness requirement, however proving
-- 2 * Cardinal.mk α = 2 * Cardinal.mk β  → Cardinal.mk α = Cardinal.mk β will involve splitting
-- into cases on α or β infinite anyway
noncomputable def iso_index_from_rank_eq {V': Type} {B: BilinForm k V} [AddCommGroup V'] [Module k V']
  {B': BilinForm k V'} (H: Hypspace B) (H': Hypspace B') (h: Module.finrank k V = Module.finrank k V')
  [FiniteDimensional k V][FiniteDimensional k V']:
  H.I ≃ H'.I := by
  apply Classical.choice
  have: 2*Fintype.card H.I=2*Fintype.card H'.I := by
    rw[<- Hypspace_finrank H,<- Hypspace_finrank H',h]
  have: Fintype.card H.I=Fintype.card H'.I := by
    omega
  exact Fintype.card_eq.mp this

protected def Basis_repr_left{B: BilinForm k V} (H: Hypspace B) (i: H.I):
  V →ₗ[k] k where
  toFun := fun v ↦ (H.basis.repr v) (Sum.inl i)
  map_add' := by simp
  map_smul' := by simp

protected noncomputable def Basis_form_right {B: BilinForm k V} (H: Hypspace B) (i: H.I):
  V →ₗ[k] k where
  toFun := fun v ↦ B v (H.basis (Sum.inr i))
  map_add' := by simp
  map_smul' := by simp

protected theorem Basis_repr_left_eq_Basis_form_right {B: BilinForm k V} (H: Hypspace B) (i: H.I):
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

theorem Hypspace_repr_left {B: BilinForm k V} (H: Hypspace B) (v: V) (i: H.I):
  (H.basis.repr v) (Sum.inl i) = B v (H.basis (Sum.inr i)) := by
    have hleft: (H.basis.repr v) (Sum.inl i) = Hyperbolic.Basis_repr_left H i v := by
      simp[Hyperbolic.Basis_repr_left]
    have hright: B v (H.basis (Sum.inr i)) = Hyperbolic.Basis_form_right H i v:= by
      simp[Hyperbolic.Basis_form_right]
    rw[hleft, hright]
    rw[Hyperbolic.Basis_repr_left_eq_Basis_form_right H i]

-- Proof should be similar to `Hypspace_repr_left`
theorem Hypspace_repr_right {B: BilinForm k V} (H: Hypspace B) (v: V) (i: H.I):
  (H.basis.repr v) (Sum.inr i) = B (H.basis (Sum.inl i)) v  := sorry

@[simp]
noncomputable def Hypsubspace_of_orthog_ind {B: BilinForm k V} {H₁: Hypsubspace B}
  {H₂: Hypsubspace B} (h: is_orthog_ind B H₁.toSubmodule  H₂.toSubmodule):
  Hypsubspace B where
  I := H₁.I ⊕ H₂.I
  coe :=
    fun i =>
    match i with
    | Sum.inl (Sum.inl j) => H₁.coe (Sum.inl j)
    | Sum.inl (Sum.inr j) => H₂.coe (Sum.inl j)
    | Sum.inr (Sum.inr j) => H₂.coe (Sum.inr j)
    | Sum.inr (Sum.inl j) => H₁.coe (Sum.inr j)
  linind := sorry
  pred := sorry

@[simp]
theorem Hypsubspace_of_direct_sum_Hypsubspaces {B: BilinForm k V}
  {H₁: Hypsubspace B} {H₂: Hypsubspace B} (h: is_orthog_ind B H₁.toSubmodule
  H₂.toSubmodule): (Hypsubspace_of_orthog_ind h).toSubmodule = H₁.toSubmodule ⊔ H₂.toSubmodule := by
    sorry

noncomputable def Hypsubspace_of_orthog_ind' {B: BilinForm k V} {H₁: Hypsubspace B}
  {H₂: Hypsubspace B} (h: is_orthog_ind_weak B H₁.toSubmodule  H₂.toSubmodule) (hr: IsRefl B):
  Hypsubspace B :=
    Hypsubspace_of_orthog_ind (is_orthog_ind_of_is_orthog_ind_weak_refl h hr)

theorem Hypsubspace_of_direct_sum_Hypsubspaces' {B: BilinForm k V}
  {H₁: Hypsubspace B} {H₂: Hypsubspace B} (h: is_orthog_ind_weak B H₁.toSubmodule
  H₂.toSubmodule) (hr: IsRefl B): (Hypsubspace_of_orthog_ind' h hr).toSubmodule = H₁.toSubmodule ⊔ H₂.toSubmodule := by
    simp only [Hypsubspace_of_orthog_ind',Hypsubspace_of_direct_sum_Hypsubspaces]


noncomputable def Hypspace_of_orthog_direct_sum' {B: BilinForm k V} {H₁: Hypsubspace B}
  {H₂: Hypsubspace B} (h: is_orthog_direct_sum B H₁.toSubmodule  H₂.toSubmodule):
  Hypspace B where
  I := H₁.I ⊕ H₂.I
  basis := sorry
  pred := sorry

noncomputable def Hypspace_of_orthog_direct_sum {B: BilinForm k V} {H₁: Hypsubspace B}
  {H₂: Hypsubspace B} (h: is_orthog_direct_sum_weak B H₁.toSubmodule  H₂.toSubmodule) (hr: IsRefl B):
  Hypspace B := Hypspace_of_orthog_direct_sum' (is_orthog_direct_sum_of_is_orthog_direct_sum_weak_refl h hr)

def hyp_pair (β:BilinForm k V) (e f : V) : Prop :=
  β e e = 0  ∧  β f f = 0  ∧  β e f = 1

-- TODO: Move to another file (and prove) or find appropriate mathlib lemma
theorem SumLinearIndependent {I J: Type} {v: I → V} {w: J → V} (hv: LinearIndependent k v)
  (hw: LinearIndependent k w) (hvw: Submodule.span k (Set.range v) ⊓ Submodule.span k (Set.range w)=⊥):
   LinearIndependent k (Sum.elim v w) := sorry

abbrev singleton := Fin 1

-- This should reduce down to 0 ≠ 1 in k
lemma hyp_pair_nonzero {β: BilinForm k V} {e f: V} (h: hyp_pair β e f) : e ≠ 0 ∧ f ≠ 0 := by
  sorry

lemma LinearIndependent_of_fun_singleton_nonzero {v: V} (h: v≠ 0):
  LinearIndependent k (fun (a: singleton) ↦ v) := sorry

@[simp]
def Hypsubspace_two {B: BilinForm k V} {e f: V} (h: hyp_pair B e f): Hypsubspace B
   where
   I := singleton
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

instance {B: BilinForm k V} {e f: V} (h: hyp_pair B e f):
  Fintype (Hypsubspace_two h).toHypspace.I := by
    simp only [Hypsubspace_two, Hypsubspace.toSubmodule, Hypsubspace.toHypspace, Hypsubspace.basis]
    exact inferInstance

theorem Hypsubspace_two_finrank_2 {B: BilinForm k V} {e f: V} (h: hyp_pair B e f):
  Module.finrank k ((Hypsubspace_two h).toSubmodule)=2 := by
  rw[Hypspace_finrank (Hypsubspace_two h).toHypspace]
  simp

-- Better name?
-- Note: This definition seems irrelevant; could be worth removing
def foo_equiv (I: Type): I ⊕ I ≃ I × (singleton ⊕ singleton) where
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




/- The below proves that a hyspace is a direct sum of Hypsubspace_two's, in the sense of
  `is_orthog_direct_sum`, that it is a direct sum as vector spaces and elements
   of differing subspaces are orthogonal.
  - Make use of (planned) theorem reducing to proving basis equivalence.

  This could be formulated in the sense of isomorphism of bilinear forms. This
  would rely on things in BilinearFormIsomorphisms not yet created.
-/

def Hypspace.hyp_pair {B: BilinForm k V} (H: Hypspace B) (i: H.I):
  hyp_pair B (H.basis (Sum.inl i)) (H.basis (Sum.inr i)) := sorry

abbrev OrthogIndexedSubspaces {ι: Type} (B:BilinForm k V) (W: ι → Submodule k V) : Prop :=
  ∀ i j, (i ≠ j) → ∀ w ∈ W i, ∀ w' ∈ W j, B w w' = 0

structure is_orthog_indexed_direct_sum {ι: Type} [DecidableEq ι]  (B: BilinForm k V) (W: ι → Submodule k V) where
  ds : DirectSum.IsInternal W
  orthog : OrthogIndexedSubspaces B W

@[simp]
def Hypspace.Hypspace_two_collection {B: BilinForm k V} (H: Hypspace B):
  H.I → Submodule k V := fun i => (Hypsubspace_two <| H.hyp_pair i ).toSubmodule

theorem Hypspace.is_orthog_indexed_direct_sum_Hypsubspace_two (B: BilinForm k V)
(H: Hypspace B) [DecidableEq H.I]: is_orthog_indexed_direct_sum B H.Hypspace_two_collection where
  ds := sorry
  orthog := sorry


/- The theorem `Hypspace_of_orthog_direct_sum` earlier proves the direct sum
    of two Hypsubspaces is a Hypspace. The below results prove this again
    in more generality.
-/

-- TODO: Move this to a better file.
@[simp]
def hyp_basis_iso {J: Type} (I: J → Type):
  (j: J)× (I j ⊕ (I j)) ≃ ((j : J) × I j ⊕ (j : J) × I j) := sorry

@[simp]
noncomputable def Hypspace_from_orthog_indexed_direct_sum_Hypsubspace {J: Type} [DecidableEq J]
(B: BilinForm k V) (W: J → Hypsubspace B)
(h: is_orthog_indexed_direct_sum B (fun j => (W j).toSubmodule)):
Hypspace B where
  I := (j: J) × (W j).I
  basis :=
    Basis.reindex (DirectSum.IsInternal.collectedBasis (h.ds) (fun j => (W j).basis)) (hyp_basis_iso (fun j ↦ (W j).I))
  pred := by
    constructor -- Note: Proof must have `hyp_basis_iso` filled in to prove
    . sorry
    . sorry
    . sorry
    . sorry
    . sorry

-- Specialization of Hypspace_from_orthog_indexed_direct_sum_Hypsubspace'
@[simp]
protected noncomputable def Hypspace_from_orthog_indexed_direct_sum_Hypsubspace_two_aux {I: Type} [DecidableEq I]
{B: BilinForm k V} {e: I → V} {f: I → V} {h: ∀ (i: I), hyp_pair B (e i) (f i)}
(h': is_orthog_indexed_direct_sum B (fun i => (Hypsubspace_two (h i)).toSubmodule  )):
Hypspace B :=
  Hypspace_from_orthog_indexed_direct_sum_Hypsubspace B (fun (i: I) => (Hypsubspace_two (h i))) h'

-- The prior definition yields a space with index type ((_: I) × singleton)
protected theorem Hypspace_from_orthog_indexed_direct_sum_Hypsubspace_two_aux_basis {I: Type} [DecidableEq I]
{B: BilinForm k V} {e: I → V} {f: I → V} {h: ∀ (i: I), hyp_pair B (e i) (f i)}
(h': is_orthog_indexed_direct_sum B (fun i => (Hypsubspace_two (h i)).toSubmodule  )):
(Hyperbolic.Hypspace_from_orthog_indexed_direct_sum_Hypsubspace_two_aux h').I = ((_: I) × singleton) := rfl

-- We will use the below theorems to create a space with a nicer index type (namely I)
@[simp]
def Hypspace.index_change {J: Type} {B: BilinForm k V} (H: Hypspace B)
  (f: H.I ≃ J): Hypspace B where
  I := J
  basis := H.basis.reindex (sum_iso f)
  pred := sorry

@[simp]
def index_iso_singleton' (I: Type): (_: I) × singleton ≃ I :=
  Equiv.sigmaUnique I fun _ ↦ singleton

@[simp]
noncomputable def Hypspace_from_orthog_indexed_direct_sum_Hypsubspace_two {I: Type} [DecidableEq I]
{B: BilinForm k V} {e: I → V} {f: I → V} {h: ∀ (i: I), hyp_pair B (e i) (f i)}
(h': is_orthog_indexed_direct_sum B (fun i => (Hypsubspace_two (h i)).toSubmodule  )):
Hypspace B := (Hyperbolic.Hypspace_from_orthog_indexed_direct_sum_Hypsubspace_two_aux h').index_change (index_iso_singleton' I)

-- Our new definition does indeed have index type I
@[simp]
theorem Hypspace_from_orthog_indexed_direct_sum_Hypsubspace_two_I {I: Type} [DecidableEq I]
{B: BilinForm k V} {e: I → V} {f: I → V} {h: ∀ (i: I), hyp_pair B (e i) (f i)}
(h': is_orthog_indexed_direct_sum B (fun i => (Hypsubspace_two (h i)).toSubmodule  )):
(Hypspace_from_orthog_indexed_direct_sum_Hypsubspace_two h').I = I := rfl


/-
  TODO: State (and prove) some theorem about recovering the hyperbolic 2 subspaces from
  Hypspace_from_orthog_direct_sum_Hypsubspace_two.

  This has to be done after the definition for Hypspace_from_orthog_direct_sum_Hypsubspace is
  created.
-/

theorem Hypspace.Nondegenerate {B:BilinForm k V}
  (H: Hypspace B) (brefl : IsRefl B) :
  Nondegenerate B := by
    intro v hv
    let b := H.basis
    have hleft: ∀ i, (b.repr v) (Sum.inl i) = 0 := by
      intro i
      rw[Hypspace_repr_left H v i]
      exact hv _
    have hright: ∀ i, (b.repr v) (Sum.inr i) = 0 := by
      intro i
      rw[Hypspace_repr_right H v i]
      rw[brefl]
      exact hv _
    have h: ∀ i, (b.repr v) i = 0
    |  Sum.inl i => hleft i
    |  Sum.inr i => hright i
    exact (Basis.forall_coord_eq_zero_iff b).mp h

-- TODO: Move to a better file location
theorem IsRefl_restrict {B: BilinForm k V} (brefl: IsRefl B) (W: Submodule k V):
  IsRefl (B.restrict W) := fun x y ↦ brefl (W.subtype x) (W.subtype y)

theorem Hypsubspace.NondegenerateOn {B:BilinForm k V}
  (brefl : IsRefl B) (H: Hypsubspace B) :
  NondegenerateOn B H.toSubmodule := by
    exact H.toHypspace.Nondegenerate (IsRefl_restrict brefl H.toSubmodule)


theorem hyp2_nondeg_refl (β:BilinForm k V)
  (brefl : IsRefl β) {e f : V} (h2: hyp_pair β e f) :
  NondegenerateOn β (Hypsubspace_two h2).toSubmodule := by
    exact (Hypsubspace_two h2).NondegenerateOn brefl


theorem hyp2_nondeg_symm (β:BilinForm k V)
  (bsymm : IsSymm β) {e f : V} (h2: hyp_pair β e f) :
  NondegenerateOn β (Hypsubspace_two h2).toSubmodule  := by
  have brefl: IsRefl β := IsSymm.isRefl bsymm
  exact hyp2_nondeg_refl β brefl h2

theorem hyp2_nondeg_alt (β:BilinForm k V)
  (balt : IsAlt β) {e f : V} (h2: hyp_pair β e f) :
  NondegenerateOn β (Hypsubspace_two h2).toSubmodule  := by
  have brefl: IsRefl β := IsAlt.isRefl balt
  exact hyp2_nondeg_refl β brefl h2

-- using `orthog_decomp` from BilinearForms, we get

def hyp2_decomp_refl (β:BilinForm k V) [FiniteDimensional k V] (brefl : IsRefl β) {e f : V} (h2:hyp_pair β e f)
  : orthog_direct_sum β (Hypsubspace_two h2).toSubmodule :=
  (orthog_decomp β (Hypsubspace_two h2).toSubmodule (hyp2_nondeg_refl  β brefl h2)) brefl

def hyp2_decomp_symm (β:BilinForm k V) [FiniteDimensional k V] (bsymm : IsSymm β) {e f : V} (h2:hyp_pair β e f)
  : orthog_direct_sum β (Hypsubspace_two h2).toSubmodule :=
  hyp2_decomp_refl β bsymm.isRefl h2

def hyp2_decomp_alt (β:BilinForm k V) [FiniteDimensional k V] (balt : IsAlt β) {e f : V} (h2:hyp_pair β e f)
  : orthog_direct_sum β (Hypsubspace_two h2).toSubmodule :=
  hyp2_decomp_refl β balt.isRefl h2


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
