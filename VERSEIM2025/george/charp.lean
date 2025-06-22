
import Matlib.Tactic

example : Field (ZMod p) := inferInstance

-- for shorthand, we can write k for this field
def kₚ  : Type := ZMod p 

instance : Field (@kₚ p) := by
  unfold kₚ
  exact inferInstance 
