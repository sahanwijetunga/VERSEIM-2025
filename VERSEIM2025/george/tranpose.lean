import Mathlib.Tactic

open LinearMap
open LinearMap (BilinForm)


variable {k : Type} [ Field k ]
variable {V V₁ V₂ : Type} 
   [ AddCommGroup V ] [ Module k V ]
   [ AddCommGroup V₁ ] [ Module k V₁ ]
   [ AddCommGroup V₂ ] [ Module k V₂ ]



lemma fintype_linear_combination_repr (v:V) {ι:Type} [Fintype ι] (b:Basis ι k V) : 
  (Fintype.linearCombination k b) (b.repr v) = v := by 
  apply Eq.trans _ (Basis.linearCombination_repr b v)
  rw [ Fintype.linearCombination_apply ]
  rw [ Finsupp.linearCombination_apply ]
  rw [ Finsupp.sum_fintype ]
  simp


structure equiv_of_spaces_with_form
(β₁:BilinForm k V₁)
(β₂:BilinForm k V₂)
where
equiv : V₁ ≃ₗ[k] V₂
compat : ∀ (v w : V₁), (β₁ v) w = (β₂ (equiv v)) (equiv w)

def equiv_from_bases (b₁:Basis ι k V₁) (b₂:Basis ι k V₂)
  : V₁ ≃ₗ[k] V₂ :=
  LinearEquiv.trans b₁.repr (b₂.repr.symm)

lemma equiv_from_bases_apply (b₁:Basis ι k V₁) (b₂:Basis ι k V₂) (i:ι) : 
  (equiv_from_bases b₁ b₂) (b₁ i) = b₂ i := by 
  unfold equiv_from_bases 
  rw [ LinearEquiv.trans_apply ]
  rw [ Basis.repr_self ]
  rw [ Basis.repr_symm_apply ]
  rw [ Finsupp.linearCombination_single ]
  apply one_smul

  

lemma equiv_of_series {ι:Type} [Fintype ι] (β:BilinForm k V) (b : Basis ι k V)
(s t : ι → k)
: (β (Fintype.linearCombination k ⇑b t)) (Fintype.linearCombination k ⇑b s) =
∑ i:ι, (∑ j:ι, (t i) * (s j) * (β (b i) (b j))) := by
unfold Fintype.linearCombination
dsimp
rw [LinearMap.BilinForm.sum_left]
apply Finset.sum_congr
rfl
intro i h
rw [LinearMap.BilinForm.sum_right]
apply Finset.sum_congr
rfl
intro j g
rw [LinearMap.BilinForm.smul_left]
rw [mul_comm]
rw [LinearMap.BilinForm.smul_right]
ring

theorem equiv_via_matrices {ι:Type} [Fintype ι] [DecidableEq ι]
  (β₁:BilinForm k V₁) (β₂:BilinForm k V₂) (b₁ : Basis ι k V₁) (i j : ι) 
  (s t : ι → k) : 
  Nonempty (equiv_of_spaces_with_form β₁ β₂) ↔ 
  ∃ b₂:Basis ι k V₂, (BilinForm.toMatrix b₁ β₁) i j = (BilinForm.toMatrix b₂ β₂) i j := by
  constructor
  
  -- mp
  intro ⟨N⟩
  let b₂ : Basis ι k V₂ := Basis.map b₁ N.equiv
  use b₂
  unfold b₂
  unfold BilinForm.toMatrix
  simp
  rw [N.compat (b₁ i) (b₁ j)]
  
  -- mpr
  intro h₁
  rcases h₁ with ⟨b₂, h₁⟩
  unfold BilinForm.toMatrix at h₁
  refine Nonempty.intro ?_
  have eq : V₁ ≃ₗ[k] V₂ := by 
     apply equiv_from_bases; exact b₁; exact b₂
  have identify_bases : ∀ i:ι, b₂ i = eq (b₁ i) := by 
     sorry
  apply equiv_of_spaces_with_form.mk
  intro v w
  swap
  exact eq
  rw [toMatrix₂_apply b₁ b₁ β₁ i j, toMatrix₂_apply b₂ b₂ β₂ i j] at h₁
  have sum_v : v = (Fintype.linearCombination k ⇑b₁) (b₁.repr v):= 
    by symm; apply fintype_linear_combination_repr
  have sum_w : w = (Fintype.linearCombination k ⇑b₁) (b₁.repr w):= 
    by symm; apply fintype_linear_combination_repr
  nth_rw 1 [sum_v, sum_w] 
  rw [equiv_of_series]
  nth_rw 2 [sum_v, sum_w]
  
  rw [ Fintype.linearCombination_apply, Fintype.linearCombination_apply]
  rw [ map_sum eq, map_sum eq] 
  rw [ Fintype.sum_congr ]

--  unfold Fintype.linearCombination
  
  --simp


  -- apply Finset.sum_congr
  -- rfl
  -- intro x h₂
  -- rw [Finset.mul_sum]
  -- apply Finset.sum_congr
  -- rfl
  -- intro y h₃
  -- rw [← identify_bases, ← identify_bases, mul_comm]
  
