--------------------------------------------------------------------------------
/-
Copyright (c) 2025 Clea Bergsman, Katherine Buesing, George McNinch, Sahan Wijetunga. All rights reserved.

Released under the Apache 2.0 license as described in the file LICENSE.

VERSEIM-2025 REU @ Tufts University
-/

import VERSEIM2025.HyperbolicBilinearForms

/-
  The purpose of this file is to create the notion of 'Odd Hyperbolic'. Essentially,
  a hyperbolic space ⊕ a one-dimensional space.

  Then, a Generalized Hyperbolic space is a Hyperbolic space or Odd Hyperbolic space. The
  use of this definition is that we can say any nondegenerate bilinear form is the direct sum
  of a a (Generalized) hyperbolic form and isotropic form.
  - I don't know if we need extra conditions like reflexive or symmetric. Probably will
    attempt symmetric first.
-/

namespace OddHyperbolic


variable {k V V': Type} [AddCommGroup V][AddCommGroup V'] [Field k] [Module k V] [Module k V']


open LinearMap (BilinForm)
open LinearMap.BilinForm
open BilinearForms -- This is the namespace in VERSEIM2025.Sahan.BilinearForms
open Hyperbolic -- This is the namespace in VERSEIM2025.HyperbolicBilinearForms
open BilinIsomorphisms -- This is the namespace in VERSEIM2025.BilinearFormIsomorphisms



/- Note: This definition may be clunky; could be worth changing. -/
@[ext]
structure OddHypspace (B: BilinForm k V) where
  hyp : Hypsubspace B
  basis : Basis ((hyp.I ⊕ hyp.I ) ⊕ singleton) k V
  compatible : hyp.coe = basis ∘ Sum.inl

def OddHypspace_pred (B: BilinForm k V): Prop
  := Nonempty ( OddHypspace B)

abbrev OddHypspace.basis_index {B: BilinForm k V} (H: OddHypspace B)
  := H.hyp.basis_index ⊕ singleton

abbrev OddHypspace.I {B: BilinForm k V} (H: OddHypspace B)
  := H.hyp.I

noncomputable def OddHypspace_of_OddHypspace_pred {B: BilinForm k V} (h: OddHypspace_pred B): OddHypspace B :=
  Classical.choice h

theorem OddHypspace_pred_of_OddHypspace {B: BilinForm k V} (H: OddHypspace B):
  OddHypspace_pred B:= ⟨H⟩

/-
  Note: This below definition `OddHypsubspace` was created purely to have a type down. It
  should probably be heavily modified before proving any of the auxillary theorems/defns
  about it.
-/
@[ext]
structure OddHypsubspace (B: BilinForm k V) where
  hyp : Hypsubspace B
  coe :  (hyp.basis_index ⊕ singleton) →  V
  compatible : hyp.coe = coe ∘ Sum.inl
  linind : LinearIndependent k coe

abbrev OddHypsubspace.basis_index {B: BilinForm k V} (H: OddHypsubspace B)
  := H.hyp.basis_index ⊕ singleton

abbrev OddHypsubspace.I {B: BilinForm k V} (H: OddHypsubspace B)
  := H.hyp.I

@[simp]
def OddHypsubspace.toSubmodule {B: BilinForm k V} (H : OddHypsubspace B) :
  Submodule k V := Submodule.span k (Set.range H.coe)

@[simp]
noncomputable def OddHypsubspace.basis {B: BilinForm k V} (H : OddHypsubspace B) :
  Basis H.basis_index k H.toSubmodule := sorry

def OddHypsubspace_of_OddHypspace_submodule  {B: BilinForm k V} {W: Submodule k V}
 (H : OddHypspace (B.restrict W)) : OddHypsubspace B := sorry

def OddHypsubspace_of_OddHypspace_submodule_toSubmodule_agrees {B: BilinForm k V} {W: Submodule k V}
 (H : OddHypspace (B.restrict W)) : (OddHypsubspace_of_OddHypspace_submodule H).toSubmodule = W := sorry

@[simp]
noncomputable def OddHypsubspace.toOddHypspace {B: BilinForm k V} (H: OddHypsubspace B):
  OddHypspace (B.restrict H.toSubmodule) where
  hyp := {
    I := H.I
    coe := fun i => ⟨ H.hyp.coe i,sorry⟩
    linind := sorry
    pred := sorry
  }
  basis := sorry
  compatible := sorry

theorem OddHypsubspace_basis_compatible {B: BilinForm k V}  (H: OddHypsubspace B):
  H.toOddHypspace.basis = H.basis := sorry

-- A `GeneralizedHypspace` is either a Hypspace or an OddHypspace.
inductive GeneralizedHypspace (B: BilinForm k V) where
  | even : Hypspace B → GeneralizedHypspace B
  | odd : OddHypspace B → GeneralizedHypspace B

def GeneralizedHypspace.I {B: BilinForm k V} (H: GeneralizedHypspace B): Type :=
  match H with
  | GeneralizedHypspace.even H => H.I
  | GeneralizedHypspace.odd H => H.I

@[simp]
def GeneralizedHypspace.basis_index {B: BilinForm k V} (H : GeneralizedHypspace B): Type :=
  match H with
  | GeneralizedHypspace.even H => H.basis_index
  | GeneralizedHypspace.odd H => H.basis_index

@[simp]
def GeneralizedHypspace.basis {B: BilinForm k V} (H : GeneralizedHypspace B): Basis H.basis_index k V :=
  match H with
  | GeneralizedHypspace.even H => H.basis
  | GeneralizedHypspace.odd H => H.basis

inductive GeneralizedHypsubspace (B: BilinForm k V)  where
  | even : Hypsubspace B → GeneralizedHypsubspace B
  | odd : OddHypsubspace B → GeneralizedHypsubspace B

def GeneralizedHypsubspace.I {B: BilinForm k V} (H: GeneralizedHypsubspace B): Type :=
  match H with
  | GeneralizedHypsubspace.even H => H.I
  | GeneralizedHypsubspace.odd H => H.I

@[simp]
def GeneralizedHypsubspace.basis_index {B: BilinForm k V} (H : GeneralizedHypsubspace B): Type :=
  match H with
  | GeneralizedHypsubspace.even H => H.basis_index
  | GeneralizedHypsubspace.odd H => H.basis_index

@[simp]
def GeneralizedHypsubspace.coe {B: BilinForm k V} (H : GeneralizedHypsubspace B): H.basis_index → V :=
  match H with
  | GeneralizedHypsubspace.even H => H.coe
  | GeneralizedHypsubspace.odd H => H.coe


@[simp]
def GeneralizedHypsubspace.toSubmodule {B: BilinForm k V} (H : GeneralizedHypsubspace B) :
  Submodule k V :=
  match H with
  | GeneralizedHypsubspace.even H => H.toSubmodule
  | GeneralizedHypsubspace.odd H => H.toSubmodule

/- Commented out code dealing with Generalized Hypsubspaces due to issues with
  things not being definitionally equal (so types didn't work out). -/

-- @[simp]
-- noncomputable def GeneralizedHypsubspace.basis {B: BilinForm k V} (H : GeneralizedHypsubspace B) :
--   Basis (H.basis_index) k H.toSubmodule := sorry

def GeneralizedHypsubspace_of_GeneralizedHypspace_submodule {B: BilinForm k V} {W: Submodule k V}
 (H : GeneralizedHypspace (B.restrict W)) : GeneralizedHypsubspace B:= sorry

def GeneralizedHypsubspace_of_GeneralizedHypspace_submodule_toSubmodule_agrees {B: BilinForm k V} {W: Submodule k V}
 (H : GeneralizedHypspace (B.restrict W)) : (GeneralizedHypsubspace_of_GeneralizedHypspace_submodule H).toSubmodule = W := sorry

-- @[simp]
-- noncomputable def GeneralizedHypsubspace.toGeneralizedHypspace {B: BilinForm k V} (H: GeneralizedHypsubspace B):
--   GeneralizedHypspace (B.restrict H.toSubmodule) :=
--   match H with
--   | GeneralizedHypsubspace.even H => GeneralizedHypspace.even H.toHypspace
--   | GeneralizedHypsubspace.odd H => GeneralizedHypspace.odd H.toOddHypspace


-- theorem GeneralizedHypsubspace_basis_index_compatible {B: BilinForm k V} (H: GeneralizedHypsubspace B):
--   H.toGeneralizedHypspace.basis_index = H.basis_index :=
--   match H with
--   | GeneralizedHypsubspace.even _ => rfl
--   | GeneralizedHypsubspace.odd _ => rfl

-- theorem GeneralizedHypsubspace_basis_compatible {B: BilinForm k V} (H: GeneralizedHypsubspace B):
--   H.toGeneralizedHypspace.basis = H.basis := sorry


end OddHyperbolic
