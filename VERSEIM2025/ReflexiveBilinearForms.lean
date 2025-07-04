--------------------------------------------------------------------------------
/-
Copyright (c) 2025 Clea Bergsman, Katherine Buesing, George McNinch, Sahan Wijetunga. All rights reserved.

Released under the Apache 2.0 license as described in the file LICENSE.

VERSEIM-2025 REU @ Tufts University
-/

import Mathlib.Tactic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import VERSEIM2025.Sahan.BilinearForms

/- Sahan: Most major results we are proving do not require reflexivity
    or require stronger assumptions like symmetric or alternating,
    however we collect some results which hold in this specific case.

    Mathlib holds many results for bilinear forms under the assumption
    of reflexivity, though it is not always needed.

    Major results (Completed)
    - A reflexive bilinear form can be written as a direct sum of 0
      and a nondegenerate bilinear form
      - `reflexive_sum_radForm_nondegenerate` (and `form_on_radForm_eq_zero`)

    Major results (Planned)
    - The quotient of a reflexive bilinear form by its radical is nondegenerate
      - `reflexive_quotient_radForm_nondegenerate`

    TODO: Clean up definitions (radForm/radForm' excessive amount of theorems?)

    TODO (LATER): Switch out VERSEIM2025.Sahan.BilinearForms for VERSEIM2025.BilinearForms
-/

open BilinearForms -- This is the namespace in VERSEIM2025.Sahan.BilinearForms
open LinearMap.BilinForm
open LinearMap (BilinForm)

variable {k V: Type*} [AddCommGroup V][Field k][Module k V]

def radForm (B: BilinForm k V) : Submodule k V where
  carrier := {v | ∀ w, B v w = 0}
  add_mem' := by simp_all
  zero_mem' := by simp_all
  smul_mem' := by simp_all

def radForm' (B: BilinForm k V) : Submodule k V where
  carrier := {v | ∀ w, B w v = 0}
  add_mem' := by simp_all
  zero_mem' := by simp_all
  smul_mem' := by simp_all

theorem radForm'_eq_radForm_flip (B: BilinForm k V) :
  radForm' B = radForm B.flip := by simp_all[radForm,radForm']

theorem radForm_eq_radForm'_flip (B: BilinForm k V) :
  radForm B = radForm' B.flip := by simp_all[radForm,radForm']

@[simp]
theorem flip_orthog_eq_orthog (B: BilinForm k V) (hr: B.IsRefl) (W: Submodule k V):
  B.flip.orthogonal W = B.orthogonal W := by
  ext x
  constructor
  . intro h
    exact fun n a ↦ hr x n (h n a)
  . intro h
    exact fun n a ↦ hr n x (h n a)

theorem radForm_eq_flip_orthogonal_top (B: BilinForm k V):
  radForm B = B.flip.orthogonal ⊤ := by
    ext x
    simp_all[BilinForm.IsOrtho,radForm]

theorem radForm'_eq_orthogonal_top (B: BilinForm k V):
  radForm' B = B.orthogonal ⊤ := by
    ext x
    simp_all[BilinForm.IsOrtho,radForm']

theorem radForm_eq_orthogonal_top (B: BilinForm k V) (hr: B.IsRefl):
  radForm B = B.orthogonal ⊤ := by
    rw[<- flip_orthog_eq_orthog B hr]
    exact radForm_eq_flip_orthogonal_top B

theorem radForm'_eq_flip_orthogonal_top (B: BilinForm k V) (hr: B.IsRefl):
  radForm' B = B.flip.orthogonal ⊤ := by
    rw[flip_orthog_eq_orthog B hr]
    exact radForm'_eq_orthogonal_top B

@[simp]
theorem radForm'_eq_radForm (B: BilinForm k V) (hr: B.IsRefl) :
  radForm' B = radForm B := by
  rw[radForm'_eq_flip_orthogonal_top _ hr, radForm_eq_flip_orthogonal_top]


theorem form_on_radForm_eq_zero (B: BilinForm k V):
  B.restrict (radForm B) = 0 := by
    ext ⟨x, hx⟩ _
    apply hx

theorem form_on_radForm'_eq_zero (B: BilinForm k V):
  B.restrict (radForm' B) = 0 := by
    ext _ ⟨y, hy⟩
    apply hy

-- Sahan: Ideally one would separate out the submodule into a definition,
-- however the choice is not canonical so it may be more difficult to construct.
-- (Note: any such definition will have to be noncomputable)
theorem reflexive_sum_radForm_nondegenerate (B: BilinForm k V) (hr: B.IsRefl):
  ∃ (W: Submodule k V), (is_orthog_direct_sum B (radForm B) W ∧ (B.restrict W).Nondegenerate) := by
    have ⟨W, h⟩ := Submodule.exists_isCompl (radForm B)
    use W
    constructor
    . constructor
      . apply (direct_sum_iff_iscompl _ _).mpr h
      . rintro ⟨a,ha⟩ ⟨b,hb⟩
        dsimp
        exact hr b a (hr a b (hr b a (hr a b (ha b))))
    intro ⟨a, ha⟩ h'
    suffices a=0 from (Submodule.mk_eq_zero W ha).mpr this
    dsimp at h'
    have: W ⊓ radForm B = ⊥ := IsCompl.inf_eq_bot (_root_.id (IsCompl.symm h))
    show a ∈ (⊥: Submodule k V)
    rw[<- this]
    constructor; . exact ha
    show ∀ b, B a b = 0
    intro b
    rw[hr]
    have: ∃ y ∈ W, ∃ z ∈ (radForm B), y + z = b := by
      have: W ⊔ (radForm B)= ⊤ := IsCompl.sup_eq_top (_root_.id (IsCompl.symm h))
      rw[<- Submodule.mem_sup]
      rw[this]
      trivial
    have ⟨y,hy,z,hz,hyz⟩ := this
    rw[<- hyz]
    calc
      (B (y + z)) a = B y a + B z a := by
        exact BilinForm.add_left y z a
      _ = 0 + 0 := by
        have: B z a = 0 := by exact hr a z (hr z a (hr a z (hr z a (hz a))))
        rw[this]
        have: B a y = 0 := by
          rw[h' ⟨y, hy⟩]
        exact congrFun (congrArg HAdd.hAdd (hr a y this)) 0
      _ = 0 := by rw[add_zero]


def quot_form {B: BilinForm k V} (hb: B.IsRefl): BilinForm k (V ⧸ (radForm B)) := sorry

theorem reflexive_quotient_radForm_nondegenerate (B: BilinForm k V) (hr: B.IsRefl):
   (quot_form hr).Nondegenerate := sorry
