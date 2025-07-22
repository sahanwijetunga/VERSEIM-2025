import Mathlib.Tactic

variable (k : Type) [ Field k ]
variable (V : Type) [ AddCommGroup V ] [ Module k V ]

variable (ι:Type) [Fintype ι]

variable (b:Basis ι k V)

-- example {v:V} (s:ι → k) (h: s = b.repr v) : (Finsupp.linearCombination k b) ↑s = v := by
--   rw [h]
--   apply Basis.linearCombination_repr 


noncomputable
example (s:ι→k) : ι →₀ k := by 
  apply Finsupp.onFinset ⊤ s  
  simp
  
example (v:V) : ι → k := b.repr v


-- example (s:ι →₀ k) : Finsupp.linearCombination k b s = ∑ (i:ι), (s i) • (b i) := by
--   apply Finsupp.linearCombination_onFinset k b (hf := by simp)


lemma myrepr (v:V) : (Fintype.linearCombination k b) (b.repr v) = v := by 
  nth_rewrite 2 [ ←Basis.linearCombination_repr b v ]
  rw [ Fintype.linearCombination_apply ]
  let s : ι →₀ k := by 
     apply  Finsupp.onFinset ⊤ (b.repr v) 
     simp
  


     
  
