-- hi
--
import Mathlib.Tactic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

open LinearMap (BilinForm)
open LinearMap

variable { K V : Type* } [Field K] [ AddCommGroup V ]  [Module K V]
variable [FiniteDimensional K V]

example (W U : Submodule K V) (v: (W ⊔ U: Submodule K V)): V := by
    have ⟨v, hv⟩ := v
    have : ∃w ∈ W, ∃ u ∈ U, w+u=v := by
        rw[Submodule.mem_sup] at hv
        exact hv
    sorry


lemma Nondegenerate.flip' {B : BilinForm K V} (hB : B.Nondegenerate) :
    B.flip.Nondegenerate := by
  intro x hx
  apply (Module.evalEquiv K V).injective
  ext f
  obtain ⟨y, rfl⟩ := (B.toDual hB).surjective f
  simpa using hx y
