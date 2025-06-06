import Mathlib.Tactic

#check neg_mem

variable (G:Type) [AddGroup G]

variable (B : AddSubgroup G)

example {x:G} : -x ∈ B →  x ∈ B := by
  convert neg_mem
  · exact Eq.symm (neg_neg x)
  · exact inferInstance -- infer NegMemClass   (not at all sure why this doesn't happend automagically)



