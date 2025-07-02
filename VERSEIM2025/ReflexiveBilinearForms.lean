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
    (or require stronger assumptions like symmetric or alternating),
    however we collect some results which hold in this specific case.

    Mathlib holds many results for bilinear forms under the assumption
    of reflexivity, though it is not always needed.

    Major results
    - A reflexive bilinear form can be written as a direct sum of 0
      and a nondegenerate bilinear form
      - `reflexive_sum_radForm_nondegenerate`
    - The quotient of a reflexive bilinear form by its radical is nondegenerate
      - `reflexive_quotient_radForm_nondegenerate`
-/


variable {k V: Type*} [AddCommGroup V][Field k][Module k V]

open LinearMap
open LinearMap (BilinForm)

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


/-- States that V is the direct sum of W and its orthogonal complement (w.r.t B)-/
structure IsOrthogDirectSum (B: BilinForm k V) (W₁ W₂: Submodule k V) where
  IsCompl : IsCompl W₁ W₂
  IsOrthog : OrthogSubspaces B W₁ W₂

theorem form_on_radForm_eq_zero (B: BilinForm k V):
  B.restrict (radForm B) = 0 := by
    ext ⟨x, hx⟩ _
    apply hx

theorem form_on_radForm'_eq_zero (B: BilinForm k V):
  B.restrict (radForm' B) = 0 := by
    ext _ ⟨y, hy⟩
    apply hy

def quot_form (B: BilinForm k V) : BilinForm k (V ⧸ (radForm B)) := sorry

theorem reflexive_quotient_radForm_nondegenerate (B: BilinForm k V) (hr: B.IsRefl)
  [FiniteDimensional k V]: (quot_form B).Nondegenerate := sorry

-- Sahan: Ideally one would separate out the submodule into a definition,
-- however the choice is not canonical so it may be more difficult to construct.
theorem reflexive_sum_radForm_nondegenerate (B: BilinForm k V) (hr: B.IsRefl)
  [FiniteDimensional k V]:
  ∃ (W: Submodule k V), (IsOrthogDirectSum B (radForm B) W ∧ (B.restrict W).Nondegenerate) := by
    sorry

open FiniteDimensional
variable {K: Type*} [Field K]
