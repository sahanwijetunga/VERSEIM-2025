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

lemma fn_image_subspace {W:Submodule k V} {f:ι → V} (hf:∀i, f i ∈ W) :
  Set.range f = promote (Set.range (fn_subspace hf)) := by 
  unfold promote
  unfold fn_subspace 
  ext
  simp  

lemma span_in_subspace {W:Submodule k V} {f : ι → V} (hf : ∀i, f i ∈ W) 
  (hspan : W = Submodule.span k (Set.range f)) :
  ⊤ ≤ Submodule.span k (Set.range (fn_subspace hf)) := by
  intro ⟨x,hw⟩ _ 
  have : x ∈ Submodule.span k (Set.range f) := by 
    rw [ ← hspan ]
    exact hw
  
 

  
noncomputable
def basis_of_subspace_basis (W:Submodule k V)
  (b:Basis_of_subspace ι W) : Basis ι k W := by
 apply Basis.mk (LinearIndep_in_subspace b.mem b.indep) 
 · intro ⟨w,hw⟩ _ 
   

example (I X: Type) (Y : Set X) (f:I → X) (hf: ∀i,f i ∈ Y) : Set ↑Y :=
  Set.range fun i => ⟨f i, hf i⟩ 

#check Basis.mk



example (I X:Type) (Y:Set X) (f:I → X) (hmem : ∀i, f i ∈ Y) : I → Y := 
  fun i => ⟨ f i , hmem i ⟩


example (I X:Type) (Y:Set X) (f:I → Y) : I → X := 
  fun i => ↑(f i)

example (X:Type) (Z Y:Set X) (h:Z ⊆ Y) : (Set ↑Y) := by 
  exact { x | x.val ∈ Z}  

  



