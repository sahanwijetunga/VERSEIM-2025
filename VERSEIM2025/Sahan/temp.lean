import Mathlib.Tactic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

open LinearMap (BilinForm)
open LinearMap.BilinForm

variable {k V: Type*} [Field k] [AddCommGroup V] [Module k V]

example {I: Type*} {B: BilinForm k V} (g : I → V) (f: I →₀ k) (v: V):
  (B ((Finsupp.linearCombination k g) f)) v
       = Finsupp.linearCombination k (fun j => B (g j) v) f := by
    sorry
    -- simp [Finsupp.linearCombination_apply, map_sum, map_smul]
    -- rw [B.map_finsupp_linearCombination]  -- distributes B over the sum
    -- Now inside the sum: B (a • g i) v = a * B (g i) v
    -- congr 1  -- reduce goal to pointwise equality inside sum
    -- ext i
    -- rw [B.map_smul]  -- scalar multiplication out of the first argument
