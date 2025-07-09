import Mathlib.Tactic

variable {k V : Type } [Field k] [AddCommGroup V] [Module k V]

variable {ι:Type} [Fintype ι] [DecidableEq ι]

structure Basis_of_subspace 
  (ι:Type) [DecidableEq ι] [Fintype ι] 
  (W: Subspace k V) where
    vecs : ι → V
    mem : ∀i, vecs i ∈ W
    indep : LinearIndependent k vecs
    span : ⊤ ≤ Submodule.span k (vecs '' ⊤)

def fun_to_subspace {W:Subspace k V} 
  (f:ι → V) (h: ∀ i, f i ∈ W) : ι → W := by
  intro i
  exact ⟨f i, h i⟩

def LinearIndep_in_subspace {W:Subspace k V}
  (f:ι → V) (hmem:∀ i, f i ∈ W) 
  (hindep: LinearIndependent k f) : 
   LinearIndependent k (fun_to_subspace f hmem) := by sorry

def Span_in_subspace (W:Subspace k V)
  (S:Set V) (hmem: S ⊂ W) (hspan : ⊤ ≤ Submodule.span k S)
  : ⊤ ≤ Submodule.span k (⟨S,hmem⟩:Set ↑W)

def basis_of_subspace_basis (W:Submodule k V)
  (b:Basis_of_subspace ι W) : Basis ι k W :=
  let vecsv : ι → W := fun_to_subspace b.vecs b.mem
  let  indep : LinearIndependent k vecsv := by
    unfold vecsv
    apply LinearIndep_in_subspace
    exact b.indep
  let span : ⊤ ≤ Submodule.span k (Submodule.span k (vecsv '' ⊤)) := by
    sorry
 Basis.mk indep b.span 

example  (W:Submodule k V)   (S:Set V) (hmem: S ⊂ W) : Set ↑W := by
  exact ⟨

#check Basis.mk
