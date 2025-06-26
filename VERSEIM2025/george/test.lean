import Mathlib.Tactic


variable { k V : Type } [Field k] [ AddCommGroup V ]  [Module k V]

variable (β:V →ₗ[k] V →ₗ[k] k)

def Alt (β:V →ₗ[k] V →ₗ[k] k) : Prop :=
  ∀ v : V, β v v = 0

def Skew (β:V →ₗ[k] V →ₗ[k] k) : Prop :=
  ∀ v w : V, β v w = - β w v

def Symm (β:V →ₗ[k] V →ₗ[k] k) : Prop :=
  ∀ v w : V, β v w = β w v

lemma skew_of_alt (β:V →ₗ[k] V →ₗ[k] k) (ha : Alt β) :
  Skew β := by 
  sorry

example [CharP k p] (hn2 : p ≠ 2) (x:V) (h:2•x = 0) : x = 0 := by
  

lemma alt_iff_skew (β:V →ₗ[k] V →ₗ[k] k) 
   [CharP k p] (hn2 : p ≠ 2)
   : Alt β ↔ Skew β := by
   constructor
   · exact skew_of_alt β 
   · intro h
     intro v
     unfold Skew at h
     have : 2*β v v = 0 := 
      calc 2*β v v = β v v + β v v := by ring
           _       = - β v v + β v v := by nth_rw 1 [h v v]
             _     = 0 by simp

     sorry



#eval (⊤:Finset (Fin 5))


example (α:Type) (f:α →₀ ℝ)  
: Finsupp.sum f (fun _ => 1) = ∑ i ∈ f.support , f i  := by refl


example (α:Type) (f:α →₀ ℝ)  [Fintype α]
: ∑ i:α, f i = ∑ i ∈ (⊤:Finset α) , f i  := by simp



#check Finsupp.sum

def disjoint_union_funs (I₁ I₂:Type) (f₁:I₁ → ℝ) (f₂:I₂→ℝ) : I₁ ⊕ I₂ → ℝ 
  | Sum.inl x => f₁ x
  | Sum.inr x => f₂ x


example : DecidableEq (ℕ × Fin 13):= inferInstance 
