import Mathlib.Tactic
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

open LinearMap
open BilinForm
open LinearMap (BilinForm)

theorem Is_Compl {k V: Type} [Field k] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]
  (B: LinearMap.BilinForm k V) (hr: B.IsRefl)
  (W: Submodule k V) (hbw: B.restrict W |>.Nondegenerate) :
     IsCompl W (B.orthogonal W) := by
    exact (BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal hr).mp hbw


namespace Hidden
variable {k V: Type} [Field k] [AddCommGroup V] [Module k V]
variable (B: LinearMap.BilinForm k V)

#check B.Nondegenerate
#check B.orthogonal

example (B : BilinForm k V) (W : Submodule k V) : BilinForm k W := by
  exact B.restrict W

end Hidden
