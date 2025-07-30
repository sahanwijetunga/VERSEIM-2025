import Mathlib.Tactic

variable {k : Type*} [ Field k ]
variable {V : Type*} [ AddCommGroup V ] [ Module k V ]

variable {ι:Type*} [Fintype ι]

variable {b:Basis ι k V}

open LinearMap
open LinearMap (BilinForm)

def fun_two {X:Type*} (x y:X) : Fin 2 → X :=
  fun i => match i with
    | 0 => x
    | 1 => y

variable {β:BilinForm k V} (h:IsRefl β)

def DimGeTwo (k V :Type*) [Field k] [AddCommGroup V] [Module k V] {ι:Type*} [Fintype ι]
  (_:Basis ι k V) : Prop 
  := 2 ≤ Module.rank k V

theorem exists_mem_ne_zero_of_rank_pos' 
  (k V :Type*) [Field k] [AddCommGroup V] [Module k V]
  (h:0 < Module.rank k V) :
  ∃ v:V, v ≠ 0 := by sorry
 

lemma quotient_by_cyclic_nontrivial (h₀ : 1 < Module.rank k V ) {v:V} (h : v ≠ 0) : 
  Nontrivial (V ⧸ Submodule.span k { v }) := by
  apply Submodule.Quotient.nontrivial_of_lt_top
  by_contra h₁
  have hcyclic : ⊤ = Submodule.span k { v} := by 
    simp_all only [ne_eq, not_lt_top_iff]
  have hrank1 : Module.finrank k (⊤:Submodule k V) = 1 := by 
    rw [ hcyclic ]
    exact finrank_span_singleton h
  rw [ Module.rank_eq_one_iff_finrank_eq_one.symm ] at hrank1
  rw [ rank_top ] at hrank1
  rw [ hrank1 ] at h₀
  exact (lt_self_iff_false _).mp h₀
  


theorem exists_lin_indep_vectors (h₀ : 1 < Module.rank k V ):
  ∃ v, ∃ w, LinearIndepOn k id ({v,w} : Set V)  := by

  have hv : ∃ v ∈ (⊤:Submodule k V), v ≠ 0 := by 
    apply exists_mem_ne_zero_of_rank_pos
    rw [ rank_top ]
    exact pos_of_gt h₀
  rcases hv with ⟨v,_,hv⟩
  use v
  let L : Submodule k V := Submodule.span k {v}
  have hw : ∃ w ∈ (⊤:Submodule k (V ⧸ L)), w ≠ 0 := by
    apply exists_mem_ne_zero_of_rank_pos --k (V ⧸ L)
    rw [ rank_top ]
    apply rank_pos_iff_nontrivial.mpr 
    apply quotient_by_cyclic_nontrivial h₀ hv
  rcases hw with ⟨w₀,hw₀⟩
  let φ : V →ₗ[k] V ⧸ L := by apply Submodule.mkQ
  let fiber :  Set V := φ ⁻¹' { w₀ }
  have p : Nonempty fiber := by 
    sorry
  let w : V := ↑(Classical.choice p)
  use w
  rw [linearIndepOn_iff]
  intro l hsupp hzero
  ext x; simp
  by_cases hl : x ∈ l.support 
  case neg => 
    simp_all only [ Submodule.mem_top
                  , ne_eq
                  , true_and
                  , Finsupp.mem_support_iff
                  , not_not
                  , L, w, fiber, φ]
  case pos => 
    have : φ 0 = φ v := by
      unfold φ
      apply  (Submodule.Quotient.eq L).mpr 
      unfold L
      aesop 
    have : (l w)•(φ ) = 
    
    
  
  


    

-- theorem has_isotropic_vector (β:BilinForm k V) {hsymm : IsSymm β} 
--   {hnd : BilinForm.Nondegenerate β} { hdim : DimGeTwo k V b} 
--   [ IsAlgClosed k ]
--   : ∃ v, v ≠ 0 ∧ β v v = 0 := by 
--   have hvnz : ∃ v₀ ∈ (⊤:Submodule k V), v₀ ≠ 0 := by 
--     apply exists_mem_ne_zero_of_rank_pos
   
  

structure hyperbolic_two_space (β:BilinForm k V) (h:IsRefl β)
  (W:Submodule k V)  where
  e : V  
  f : V
  isotropic : β e e = 0 ∧ β f f = 0
  nondeg : (β: BilinForm k V) e f = 1
  lin_indep : LinearIndependent k (fun_two e f)
  span : W = Submodule.span k { e , f }



structure hyperbolic_space (β:BilinForm k V) (h:IsRefl β)
  {ι:Type} {b:Basis ι k V} [Fintype ι] {even: Even (Fintype.card ι)}
  

-- theorem symm_or_alt_of_reflexive (β:BilinForm k V) ( h : IsRefl β ): 
--  IsSymm β ∨ IsAlt β := by
  
--   have id₁ (x y z : V) : β x ( (β x y)• z - (β x z) • y ) = 0 := by calc 
--     β x ( (β x y)• z - (β x z) • y) = (β x y) * (β x z) - (β x z) * ( β x y) := by simp
--                                   _ = 0 := by ring

--   have id₂ (x y z : V) : β ((β x y) • z - (β x z) • y) x = 0 := by 
--     apply LinearMap.IsRefl.eq_zero h (id₁ x y z)

--   have id₃ (x y z : V) : (β x y) * (β z x) = (β x z) * (β y x) := by
--     suffices h : (β x y) * (β z x) - (β x z) * (β y x) = 0 by grind
--     have : (β ((β x) y • z - (β x) z • y)) x = 0 := id₂ x y z
--     rw [ β.sub_left ] at this
--     rw [ β.smul_left, β.smul_left ] at this
--     exact this

--   have id₄ (x y : V) : (β x y)*(β x x) =  (β y x)*(β x x) := by
--     rw [ id₃ x y x ] 
--     ring
  
--   have hs (x y : V) (hx : β x x ≠ 0) : β x y = β y x := by
--     apply mul_right_cancel₀ hx 
--     exact id₄ x y

   
--   by_cases ks:β.IsSymm 
--   case pos => exact Or.inl ks
--   case neg => 

--     apply Or.intro_right

--     have hxxyy (x y : V) (h: β x y ≠ β y x) : β x x = 0 ∧ β y y = 0 := by 
--       constructor
--       case left => sorry
--       case right => sorry

--     by_contra l

--     have hue : ∃ u, β u u ≠ 0 := not_forall.mp l
--     rcases hue with ⟨u,hu⟩

--     have lvw : ∃ v w, β v w ≠ β w v := not_symm.mp ks
--     rcases lvw with ⟨ v, w, hvw ⟩

--     have huv : β u v = β v u := by exact hs u v hu
--     have huw : β u w = β w u:= by exact hs u w hu 

--     have hvw₂ : (β v w) * (β u v) = (β v u) * (β w v) := id₃ _ _ _
--     have hvw₃ : (β w v) * (β u w) = (β w u) * (β v w) := id₃ _ _ _    

--     rw [ huv, mul_comm ] at hvw₂ 
--     rw [ huw, mul_comm ] at hvw₃
        
--     have hv₁ : β v u = 0 := by apply eq_zero_of_no_cancel hvw hvw₂

--     have hv₂ : β w u = 0 := by apply eq_zero_of_no_cancel hvw.symm hvw₃ 

--     have : β (u+v) w ≠ f (u+v w) := 
    

lemma not_symm {X:Type*} {f : X → X → Prop} :
  (¬ ∀ x y, f x y ) ↔ ( ∃ x y, ¬ f x y ) := by
  simp_all only [not_forall]

lemma eq_zero_of_no_cancel {a b c : k} (_:b ≠ c) (_:a*b = a*c ) : a = 0 := by
  simp_all only [ne_eq, mul_eq_mul_left_iff, false_or]
  
lemma rearrange (a b c : k) (h:a*b = a*c) : a*(b-c) = 0 := by calc
  a*(b-c) = a*b - a*c := by ring
        _ = 0 := by rw [h]; ring

/-- This is lemma 2.6 in Grove - "Classical Groups and Geometric Algebra"
-/
lemma grove_lemma (β:BilinForm k V) (h : ∀ u v w : V, (β u v)*(β w u) = (β v u)*(β u w)) :
  IsSymm β ∨ IsAlt β := by
   have id₁ (v w : V) : (β v v)*(β w v) = (β v v)*(β v w)  :=  h v v w
   by_cases c₁ : ∀ v w, β v w = β w v
   case pos  => 
     apply Or.inl c₁     
   case neg  => 
     suffices h₁ : (∀ v w, β v w = β w v) ∨ (∀ u, β u u = 0 )  by
       exact h₁ 
     by_contra h₁
     rcases not_or.mp h₁ with ⟨ hvw, hu ⟩
     rw [ not_symm ] at hvw 
     rw [ not_forall ] at hu 

     rcases hvw with ⟨x,z,hxz⟩  -- β x z ≠ β z x
     rcases hu with ⟨y,hy⟩      -- β y y ≠ 0

     have hx0 : β x x = 0 := eq_zero_of_no_cancel hxz (id₁ x z).symm

     have hz0 : β z z = 0 := eq_zero_of_no_cancel hxz (id₁ z x)

     have hxy : β x y = β y x := by apply mul_left_cancel₀ hy (id₁ y x)

     have hzy : β y z = β z y := by apply mul_left_cancel₀ hy (id₁ y z).symm
     
  
     
     

--------------------------------------------------------------------------------
    
example (h: ¬ ∀ x y:V, β x y = β y x) : ∃ (x y : V), β x y ≠ β y x := by
  have : ∃ x, ¬ ∀ y, β x y = β y x := by 
    apply not_forall.mp h
  rcases this with ⟨x,hx⟩
  use x
  apply not_forall.mp hx


example (hs: ¬ β.IsSymm) : ∃ x y:V, β x y ≠ β y x := by 
  have : ∃ x, ¬ ∀ y, β x y = β y x := by 
    apply not_forall.mp hs
  rcases this with ⟨x,hx⟩
  use x
  apply not_forall.mp hx


lemma hyp_is_nondeg (W:Submodule k V) (β:BilinForm k V) { h : IsRefl β } (hyp : hyperbolic_two_space β  h W) : 
  Nondegenerate (β.restrict W) := by 
    sorry
  

example (a b  : k) (h: a - b = 0)  : a = b := by grind
