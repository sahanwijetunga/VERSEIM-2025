import Mathlib.Tactic

variable {k V : Type} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]

--open Module



example ( W : Submodule k V) (s:Set W) : Set V :=  by
  exact { x:V | x ∈ W}

example (W:Submodule k V) (w:W) : V := ↑w


-- f is defined up here for this problem

def f {n m:ℕ} {W₁ W₂ : Submodule k V} (s₁:Fin n →  W₁) (s₂: Fin m → W₂) :
  (Fin n) ⊕ (Fin m) → V := by
    intro i
    match i with
     | Sum.inl x => exact ↑(s₁ x)
     | Sum.inr y => exact ↑(s₂ y)

lemma union_span (n m:ℕ) (W₁ W₂ : Submodule k V) (s₁:Fin n →  W₁) (s₂: Fin m → W₂)
      (h₁:(⊤:Submodule k W₁) = Submodule.span k (s₁ '' ⊤))
      (h₂:(⊤:Submodule k W₂) = Submodule.span k (s₂ '' ⊤))
      (h₃:⊤ = W₁ ⊔ W₂)
    : (⊤:Submodule k V) = Submodule.span k ((f s₁ s₂) '' ⊤)  := by
    have h₄ : W₁ + W₂ = ⊤ := by
      simp
      rw[h₃]
    ext v
    rw[h₃]
    rw[Submodule.mem_sup]
    constructor
    · intro h₅ --x₀-- h₆
      unfold f
      simp
      sorry
    · simp
      intro h₅
      sorry

lemma union_span' /- (n m :ℕ) -/ (W₁ W₂ : Submodule k V) (s₁ s₂ : Set V)
  /- (h₁:∀ x ∈ s₁, s ∈ W₁) (h₂:∀ x∈s₂, s∈ W₂) -/
  (hs₁: W₁ = Submodule.span k s₁)
  (hs₂: W₂ = Submodule.span k s₂)
  (hw: ⊤ = W₁ ⊔ W₂)
  : ⊤ = Submodule.span k (s₁ ∪ s₂) := by
    ext v
    rw[hw]
    rw[Submodule.mem_sup]
    constructor
    · intro h₃
      rw[Submodule.span_union]
      rw[← hs₁]
      rw[← hs₂]
      rw[← hw]
      trivial
    · intro h₃
      rw[Submodule.span_union] at h₃
      rw[← hs₁] at h₃
      rw[← hs₂] at h₃
      rw[← Submodule.mem_sup]
      exact h₃


#check Submodule.mem_sup
    --intro X h₄
    --simp at h₄
    -- rw[Submodule.span_union




      --do we need disjoint functions here



def disjointUnion_funs {ι₁ ι₂ X: Type} ( f₁:ι₁ → X) (f₂:ι₂ → X) (u: ι₁ ⊕ ι₂) : X :=
   match u with
    | Sum.inl x => f₁ x
    | Sum.inr y => f₂ y

theorem lin_indep_by_transverse_subspaces
   (k V : Type) [Field k] [AddCommGroup V] [Module k V] (I₁ I₂ : Type)
   [Fintype I₁] [Fintype I₂]
   (b₁ : I₁ → V) (b₂ : I₂ → V)
   (b1_indep : LinearIndependent k b₁)
   (b2_indep : LinearIndependent k b₂)
   (W₁ W₂ : Submodule k V)
   (h_int : W₁ ⊓ W₂ = ⊥)
   (hbw1 : ∀ i, b₁ i ∈ W₁)
   (hbw2 : ∀ i, b₂ i ∈ W₂)
   [DecidableEq I₁] [DecidableEq I₂]
   : LinearIndependent k (Sum.elim b₁ b₂) := by
    rw[linearIndependent_iff'']
    intro s a g h₁ t
    have k₀ : ∑ i ∈ s, a i • Sum.elim b₁ b₂ i = ∑ i : (I₁ ⊕ I₂), a i • Sum.elim b₁ b₂ i := by
      rw[h₁]
      have k₀₀ : Disjoint s sᶜ := by
        unfold Disjoint
        intro r
        simp
        intro y₀ y₁
        ext x
        simp
        intro hx
        have xnotins : x ∈ Finset.univ \ s := y₁ hx
        simp at xnotins
        exact xnotins (y₀ hx)
      have k₀₁ : s ∪ sᶜ = (⊤ : Finset (I₁ ⊕ I₂)) := by
        simp
      have k₀₂ : (⊤: Finset (I₁ ⊕ I₂)) = Finset.univ := by
        simp
      rw[k₀₂] at k₀₁
      rw[ ← k₀₁]
      rw[Finset.sum_union k₀₀]
      rw[h₁]
      have k₀₃ : ∀ i ∈ sᶜ, a i = 0 := by
        intro i h
        rw[g]
        intro p
        rw[Finset.mem_compl] at h
        exact h p
      simp
      rw[Finset.sum_eq_zero]
      intro x₀ h
      rw[k₀₃]
      simp
      exact h
    have eq_h : ∑ a₁, a (Sum.inl a₁) • Sum.elim b₁ b₂ (Sum.inl a₁) +
    ∑ a₂, a (Sum.inr a₂) • Sum.elim b₁ b₂ (Sum.inr a₂) =
    ∑ i, (a (Sum.inl i)) • (b₁ i) + ∑ j, (a (Sum.inr j)) • (b₂ j) := by
      simp
    have k₁ : ∑ i, (a (Sum.inl i)) • (b₁ i) = - ∑ j, (a (Sum.inr j)) • (b₂ j)  := by
      rw[k₀] at h₁
      simp at h₁
      rw[add_eq_zero_iff_eq_neg'] at h₁
      rw[h₁]
      simp
    have k₂ : ∑ i, (a (Sum.inl i)) • (b₁ i) ∈ W₁ ⊓ W₂ := by
      simp
      have k₂₀ : ∑ i, (a (Sum.inl i)) • (b₁ i) ∈ W₁ := by
        exact Submodule.sum_smul_mem W₁ (fun i ↦ a (Sum.inl i)) fun c a ↦ hbw1 c
      have k₂₁ : ∑ i, (a (Sum.inl i)) • (b₁ i) ∈ W₂ := by
        rw[k₁]
        apply Submodule.neg_mem
        exact Submodule.sum_smul_mem W₂ (fun i ↦ a (Sum.inr i)) fun c a ↦ hbw2 c
      constructor
      · exact k₂₀
      · exact k₂₁
    have k₃ : - ∑ j, (a  (Sum.inr j)) • (b₂ j) ∈ W₁ ⊓ W₂ := by
      rw[k₁] at k₂
      exact k₂
    rw[linearIndependent_iff''] at b1_indep
    rw[linearIndependent_iff''] at b2_indep
    rw[h_int] at k₂
    rw[h_int] at k₃
    simp at k₂
    simp at k₃
    apply b1_indep at k₂
    apply b2_indep at k₃
    match t with
      | Sum.inl x =>
        rw[k₂]
      | Sum.inr x =>
        rw[k₃]
    · simp
    · simp


#check lin_indep_by_transverse_subspaces
#check Basis

/- noncomputable
example (W₁ W₂ : Submodule k V)
        (ι₁ ι₂ : Type) [Fintype ι₁] [Fintype ι₂]
        (B₁ : Basis ι₁ k W₁)
        (B₂ : Basis ι₂ k W₂)

        (f₁:ι₁ → V) (f₂:ι₂ → V)
        (hi₁:LinearIndependent k f₁) (hi₂:LinearIndependent k f₂)
        [DecidableEq ι₁] [DecidableEq ι₂]

        (hspan : W₁ ⊔ W₂ = (⊤:Set V))
        (hindep : W₁ ⊓ W₂ = (⊥:Set V)) :
      Basis (ι₁ ⊕ ι₂) k V := by
      have hli: LinearIndependent k (disjointUnion_funs f₁ f₂) := by
        apply lin_indep_by_transverse_subspaces
        · exact hi₁
        · exact hi₂
        · sorry
        · sorry
        ·
          sorry
        · exact W₁
        · exact W₂

        /- rw[linearIndependent_iff'']
        intro S g h₀ h₁ y
        by_cases y ∈ S
        · sorry
        · sorry -/
      have hsp: ⊤ ≤ Submodule.span k (Set.range (disjointUnion_funs f₁ f₂)) := by
        simp
        -- have k₀: Set.range (disjointUnion_funs f₁ f₂) = s ∪
        sorry


      exact Basis.mk hli hsp
-/

def disjointUnion_funs' {ι₁ ι₂ : Type} {k V : Type} [Field k] [AddCommGroup V]
[Module k V]  {W₁ W₂ : Submodule k V} (f₁ : ι₁ → W₁ ) (f₂ : ι₂ → W₂) (u: ι₁ ⊕ ι₂) : V :=
  match u with
  | Sum.inl x => f₁ x
  | Sum.inr y => f₂ y

variable (k V : Type) [Field k] [AddCommGroup V] [Module k V]

#check disjointUnion_funs'

noncomputable
example (W₁ W₂ : Submodule k V)
        (ι₁ ι₂ : Type) [Fintype ι₁] [Fintype ι₂]
        (B₁ : Basis ι₁ k W₁)
        (B₂ : Basis ι₂ k W₂)
        (hspan : W₁ ⊔ W₂ = (⊤: Submodule k V))
        (hindep : W₁ ⊓ W₂ = (⊥:Submodule k V))
        [DecidableEq ι₁] [DecidableEq ι₂]:
       Basis (ι₁ ⊕ ι₂) k V := by
      have hli: LinearIndependent k (Sum.elim (W₁.subtype ∘ B₁) (W₂.subtype ∘ B₂)) := by
        apply lin_indep_by_transverse_subspaces
        · apply LinearIndependent.map' B₁.linearIndependent W₁.subtype (by simp)
        · apply LinearIndependent.map' B₂.linearIndependent W₂.subtype (by simp)
        · have k₀ : Disjoint W₁ W₂ := by
            rw[disjoint_iff]
            exact hindep
          rw[Disjoint.eq_bot k₀]
        · simp
        · simp
      have hsp: ⊤ ≤ Submodule.span k (Set.range (Sum.elim (W₁.subtype ∘ B₁) (W₂.subtype ∘ B₂))) := by
        simp
        ext v
        simp
        have hs₁ : W₁ = Submodule.span k (Set.range (Subtype.val ∘ ⇑B₁)) := by
          sorry
        have hs₂ : W₂ = Submodule.span k (Set.range (Subtype.val ∘ ⇑B₂)) := by
          sorry

        rw[union_span' 1 2 hs₁ W₁ hs₂ hspan]
        -- failed to synthesize finite dimensional???

        by_cases h:  v ∈ W₁
        ·
          --rw[Set.range_comp, Set.range_comp]
          --rw[Submodule.span_union]

          #check union_span'

          suffices vmem: (v ∈ Submodule.span k (Set.range (Subtype.val ∘  ⇑B₁))) from ?_
          ·  exact Submodule.mem_sup_left vmem
          /-
          suffices vmem: (v ∈ Submodule.span k (Subtype.val ∘  Set.range ⇑B₁)) from ?_
          ·  exact Submodule.mem_sup_left vmem
          -/


          /- have k₁ : Submodule.span k (Set.range (Subtype.val ∘ ⇑B₁)) = Submodule.map (W₁.subtype) (Submodule.span k (Set.range (⇑B₁))) := by
            simp
            sorry -/

          rw[Submodule.apply_mem_span_image_iff_mem_span Subtype.val]
          #check Submodule.span_image'

          #check Basis.span_eq
          #check Basis.mem_span



          rw[Submodule.mem_span]
          intro X g
          rw[Set.union_subset_iff] at g
          rcases g with ⟨ g₁,  g₂ ⟩
          --rw[Set.range_comp] at g₁
          /- have k₀: v ∈ (Set.range ⇑ B₁) := by
            sorry  -/
          --Set.mem_image_of_mem
          --apply Set.range_comp_subset_range at g₁
          have k₀: (Set.range ⇑ B₁ ) ⊆  (⊤ : Set W₁ ) := by
            simp
          rw[k₀] at g₁
          #check Basis.span_eq
          #check Basis.mem_span
          sorry
        ·
          sorry


      exact Basis.mk hli hsp



#check
