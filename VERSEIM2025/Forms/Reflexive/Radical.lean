--------------------------------------------------------------------------------
/-
Copyright (c) 2025 Clea Bergsman, Katherine Buesing, George McNinch, Sahan Wijetunga. All rights reserved.

Released under the Apache 2.0 license as described in the file LICENSE.

VERSEIM-2025 REU @ Tufts University
-/

import Mathlib.Tactic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import VERSEIM2025.Forms.Bilinear

/-
  Major results (Completed)
  - A reflexive bilinear form can be written as a direct sum of 0
    and a nondegenerate bilinear form
    - `reflexive_sum_radForm_nondegenerate` (and `form_on_radForm_eq_zero`)
  - The quotient of a reflexive bilinear form by its radical is nondegenerate
    - `reflexive_quotient_radForm_nondegenerate`

  TODO: Clean up definitions (radForm/radForm' excessive amount of theorems?)
-/

open BilinearForms -- This is the namespace in VERSEIM2025.Forms.Hyperbolic.BilinearForms
open LinearMap.BilinForm
open LinearMap (BilinForm)

variable {R M: Type*} [AddCommGroup M][CommRing R] [Module R M]
variable {F V: Type*} [Field F] [AddCommGroup V] [Module F V]

def radForm (B: BilinForm R M) : Submodule R M where
  carrier := {v | ∀ w, B v w = 0}
  add_mem' := by simp_all
  zero_mem' := by simp_all
  smul_mem' := by simp_all

def radForm' (B: BilinForm R M) : Submodule R M where
  carrier := {v | ∀ w, B w v = 0}
  add_mem' := by simp_all
  zero_mem' := by simp_all
  smul_mem' := by simp_all

theorem radForm_eq_kernel (B: BilinForm R M): radForm B = LinearMap.ker B := by
  ext x; simp[radForm]
  constructor
  . intro h
    ext w
    simp_all [LinearMap.zero_apply]
  . simp_all [LinearMap.zero_apply]

theorem radForm'_eq_radForm_flip (B: BilinForm R M) :
  radForm' B = radForm B.flip := by simp_all[radForm,radForm']

theorem radForm_eq_radForm'_flip (B: BilinForm R M) :
  radForm B = radForm' B.flip := by simp_all[radForm,radForm']

@[simp]
theorem flip_orthog_eq_orthog (B: BilinForm R M) (hr: B.IsRefl) (W: Submodule R M):
  B.flip.orthogonal W = B.orthogonal W := by
  ext x
  constructor
  . intro h
    exact fun n a ↦ hr x n (h n a)
  . intro h
    exact fun n a ↦ hr n x (h n a)

theorem radForm_eq_flip_orthogonal_top (B: BilinForm R M):
  radForm B = B.flip.orthogonal ⊤ := by
    ext x
    simp_all[BilinForm.IsOrtho,radForm]

theorem radForm'_eq_orthogonal_top (B: BilinForm R M):
  radForm' B = B.orthogonal ⊤ := by
    ext x
    simp_all[BilinForm.IsOrtho,radForm']

theorem radForm_eq_orthogonal_top (B: BilinForm R M) (hr: B.IsRefl):
  radForm B = B.orthogonal ⊤ := by
    rw[<- flip_orthog_eq_orthog B hr]
    exact radForm_eq_flip_orthogonal_top B

theorem radForm'_eq_flip_orthogonal_top (B: BilinForm R M) (hr: B.IsRefl):
  radForm' B = B.flip.orthogonal ⊤ := by
    rw[flip_orthog_eq_orthog B hr]
    exact radForm'_eq_orthogonal_top B

@[simp]
theorem radForm'_eq_radForm (B: BilinForm R M) (hr: B.IsRefl) :
  radForm' B = radForm B := by
  rw[radForm'_eq_flip_orthogonal_top _ hr, radForm_eq_flip_orthogonal_top]


theorem form_on_radForm_eq_zero (B: BilinForm R M):
  B.restrict (radForm B) = 0 := by
    ext ⟨x, hx⟩ _
    apply hx

theorem form_on_radForm'_eq_zero (B: BilinForm R M):
  B.restrict (radForm' B) = 0 := by
    ext _ ⟨y, hy⟩
    apply hy

-- Name could be improved
theorem orthog_direct_sum_of_radForm_isCompl (B: BilinForm F V)
  (W: Submodule F V) (hW: IsCompl (radForm B) W): is_orthog_direct_sum_weak B (radForm B) W := by
  constructor
  . apply (direct_sum_iff_iscompl _ _).mpr hW
  . rintro a ha b hb
    exact ha b

theorem Nondegenerate_of_isCompl_of_radForm (B: BilinForm R M) (hr: B.IsRefl)
  (W: Submodule R M) (hW: IsCompl (radForm B) W): (B.restrict W).Nondegenerate := by
    intro ⟨a, ha⟩ h'
    suffices a=0 from (Submodule.mk_eq_zero W ha).mpr this
    dsimp at h'
    have: W ⊓ radForm B = ⊥ := IsCompl.inf_eq_bot (_root_.id (IsCompl.symm hW))
    show a ∈ (⊥: Submodule R M)
    rw[<- this]
    constructor; . exact ha
    show ∀ b, B a b = 0
    intro b
    have: ∃ y ∈ W, ∃ z ∈ (radForm B), y + z = b := by
      have: W ⊔ (radForm B)= ⊤ := IsCompl.sup_eq_top (_root_.id (IsCompl.symm hW))
      rw[<- Submodule.mem_sup]
      rw[this]
      trivial
    have ⟨y,hy,z,hz,hyz⟩ := this
    rw[<- hyz]
    calc
      (B a (y + z)) = B a y + B a z := by
        exact add_right a y z
      _ = 0 + 0 := by
        have: B a z = 0 := hr z a (hz a) -- Note: this is the only place we need reflexivity
        rw[this]
        have: B a y = 0 := by
          exact h' ⟨y, hy⟩
        rw[this]
      _ = 0 := by rw[add_zero]


-- Ideally one would separate out the submodule into a definition,
-- however the choice is not canonical so it may be more difficult to construct.
-- (Note: any such definition will have to be noncomputable)
-- (Note: is_orthog_direct_sum and is_orthog_direct_sum' are equivalent given Reflexivity)
theorem sum_radForm_nondegenerate  (B: BilinForm F V) (hr: B.IsRefl):
  ∃ (W: Submodule F V), (is_orthog_direct_sum B (radForm B) W ∧ (B.restrict W).Nondegenerate) := by
    have ⟨W, h⟩ := Submodule.exists_isCompl (radForm B)
    use W
    constructor
    . refine is_orthog_direct_sum_of_is_orthog_direct_sum_weak_refl ?_ hr
      exact orthog_direct_sum_of_radForm_isCompl B W h
    exact Nondegenerate_of_isCompl_of_radForm B hr W h

def quot_form {B: BilinForm R M} (hb: B.IsRefl): BilinForm R (M ⧸ (radForm B)) :=
  (Submodule.liftQ _ (LinearMap.flip (Submodule.liftQ _ B (by rw[radForm_eq_kernel B]  )))
  ( by
    nth_rewrite 1[radForm_eq_kernel B]
    intro v hv
    ext w
    apply hb
    simp_all
  )
  ).flip


def quot_form_apply {B: BilinForm R M} (hb: B.IsRefl) (v w: M):
(quot_form hb) (Submodule.Quotient.mk v) (Submodule.Quotient.mk w) = B v w := by
  simp[quot_form]

def quot_form_apply' {B: BilinForm R M} (hb: B.IsRefl):
  B = (quot_form hb).comp (radForm B).mkQ (radForm B).mkQ := by
  ext v w
  exact quot_form_apply hb v w

theorem reflexive_quotient_radForm_nondegenerate (B: BilinForm R M) (hr: B.IsRefl):
   (quot_form hr).Nondegenerate := by
  intro v hv
  induction' v using Submodule.Quotient.induction_on with v
  suffices v ∈ radForm B from ?_
  . simpa using this
  have: ∀ w, B v w = 0 := by
    intro w
    have: ((quot_form hr) (Submodule.Quotient.mk v)) (Submodule.Quotient.mk w) = 0 := by
      exact hv (Submodule.Quotient.mk w)
    simpa using this
  exact this
