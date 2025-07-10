import Mathlib.Tactic

import Mathlib.Tactic
import Mathlib.Data.Matrix.Rank


variable {k V : Type} [Field k] [AddCommGroup V] [Module k V]

variable {ι:Type} [Fintype ι] [DecidableEq ι]

variable {b:Basis ι k V}

open LinearMap 
open LinearMap (BilinForm)

example (β:BilinForm k V) : Matrix.transpose (BilinForm.toMatrix b β) = 
        (LinearMap.toMatrix b (Basis.dualBasis b) β ) := by 
  ext
  rw [ LinearMap.toMatrix_apply ] 
  simp

example (β:BilinForm k V) : Module.rank (range β) = 
        Matrix.rank (BilinForm.toMatrix b β) := by
g

