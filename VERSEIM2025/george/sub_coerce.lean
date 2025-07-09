import Mathlib.Tactic

variable {k V : Type } [Field k] [AddCommGroup V] [Module k V]

variable {ι:Type}

structure Basis_of_subspace
  (ι:Type) 
  (W: Subspace k V) where
    vecs : ι → V
    mem : ∀i, vecs i ∈ W
    indep : LinearIndependent k vecs
    span : W = Submodule.span k (Set.range vecs)

def fn_subspace {W:Submodule k V} {f:ι → V} (hf:∀i, f i ∈ W) :
  ι → ↑W := fun j => ⟨f j, hf j⟩

def promote {W:Submodule k V} (S:Set ↑W) : Set V := 
  let incl : ↑W → V := fun x => ↑x
  incl '' S

def LinearIndep_in_subspace 
  {W:Subspace k V}
  {f:ι → V} (hmem : ∀ i, f i ∈ W) 
  (hindep: LinearIndependent k f) : 
   LinearIndependent k (fn_subspace hmem) := by 
     sorry

lemma image_in  {W:Submodule k V} {f:ι → V} (hf:∀i, f i ∈ W) :
  Set.range f ⊆ W := by 
  intro x hx
  have : ∃ i, f i = x:=  Set.mem_range.mp hx
  rcases this with ⟨i,hi⟩
  apply Set.mem_of_eq_of_mem 
  · exact Eq.symm hi
  · exact hf i
  

lemma span_in_subspace {W:Submodule k V} {f : ι → V} (hf : ∀i, f i ∈ W) 
  (hspan : W = Submodule.span k (Set.range f)) :
  (⊤:Set ↑W) ≤ Submodule.span k (Set.range (fn_subspace hf)) := by
  intro ⟨x,hw⟩ _ 
  have : x ∈ Submodule.span k (Set.range f) := by 
    rw [ ← hspan ]
    exact hw
  apply Submodule.mem_span.mpr
  intro p hsubp
  --have : promote (Set.range (fn_subspace hf)) ⊂ (p:Submodule k V) := sorry
  sorry
 

  
noncomputable
def basis_of_subspace_basis (W:Submodule k V)
  (b:Basis_of_subspace ι W) : Basis ι k W := by
 apply Basis.mk (LinearIndep_in_subspace b.mem b.indep) 
 · intro ⟨w,hw⟩ _ 
   sorry
   

example (I X: Type) (Y : Set X) (f:I → X) (hf: ∀i,f i ∈ Y) : Set ↑Y :=
  Set.range fun i => ⟨f i, hf i⟩ 

#check Basis.mk



example (I X:Type) (Y:Set X) (f:I → X) (hmem : ∀i, f i ∈ Y) : I → Y := 
  fun i => ⟨ f i , hmem i ⟩


example (I X:Type) (Y:Set X) (f:I → Y) : I → X := 
  fun i => ↑(f i)

example (X:Type) (Z Y:Set X) (h:Z ⊆ Y) : (Set ↑Y) := by 
  exact { x | x.val ∈ Z}  

example (X :Type) (Y:Set X) (Z: Set Y) : Set X :=  Set.image id Z
  
example (W:Subspace k V) : Function.Injective W.subtype := by simp 


example (W:Subspace k V) : ⊥ = LinearMap.ker  W.subtype := by simp


def convert {ι:Type} {W:Submodule k V} {f:ι → V} (hf:∀i, f i ∈ W) 
  : ι → ↑W 
  | i => ⟨f i, hf i⟩

example (ι:Type) (W:Submodule k V) (f:ι → V) (hf:∀i, f i ∈ W) 
  : f = W.subtype ∘ (fun i => ⟨f i, hf i⟩) := by 
  ext
  simp
  
example (ι:Type) (W:Submodule k V) (f:ι → V) (hf:∀i, f i ∈ W) (hindep : LinearIndependent k f)
  :  LinearIndependent k (fun i => (⟨f i, hf i⟩:↑W)) := by 
  
  sorry
