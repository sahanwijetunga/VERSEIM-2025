import Mathlib.Tactic

variable {k : Type} [ Field k ]
variable {V : Type} [ AddCommGroup V ] [ Module k V ]

variable {ι:Type} [Fintype ι]

variable {b:Basis ι k V}

/--  Get the conclusion of ‘theorem Basis.linearCombination_repr‘ but
with ‘Fintype.linearCombination‘ rather than ‘Finsupp.linearCombination‘
--/
lemma fintype_linear_combination_repr (v:V) : (Fintype.linearCombination k b) (b.repr v) = v := by 
  apply Eq.trans _ (Basis.linearCombination_repr b v)
  rw [ Fintype.linearCombination_apply ]
  rw [ Finsupp.linearCombination_apply ]
  rw [ Finsupp.sum_fintype ]
  simp


     
  
