import Mathlib.Tactic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal


def hyp_pair (β:BilinForm k V) (e f : V) : Prop :=
  β e e = 0  ∧  β f f = 0  ∧  β e f = 1

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
