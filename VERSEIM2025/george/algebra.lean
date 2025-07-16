import Mathlib.Tactic

variable {F E : Type} [Field F] [Field E] [Algebra F E]

variable {V :Type } [AddCommGroup V] [Module F V]

noncomputable section

open TensorProduct
open Polynomial


example : Module E (E⊗[F] F) := inferInstance

example : Module F[X] (F[X] ⊗[F] V) := inferInstance

