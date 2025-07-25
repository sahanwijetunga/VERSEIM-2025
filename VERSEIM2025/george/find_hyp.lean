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


structure hyperbolic_two_space (β:BilinForm k V) (h:IsRefl β)
  (W:Submodule k V)  where
  e : V  
  f : V
  isotropic : β e e = 0 ∧ β f f = 0
  nondeg : (β: BilinForm k V) e f = 1
  lin_indep : LinearIndependent k (fun_two e f)
  span : W = Submodule.span k { e , f }

lemma not_symm {X:Type*} {f : X → X → Prop}
  (h : ¬ ∀ x y, f x y ) : ∃ x y, ¬ f x y := by
  rcases not_forall.mp h with ⟨ x , hx ⟩
  use x
  apply not_forall.mp hx


lemma not_symm' (X:Type*) (f:X → X → Prop)
  (h : ¬ ∀ (z: (_:X) × X), f z.fst z.snd ) : ∃ z:(_:X) × X, ¬ f z.fst z.snd := by
  apply not_forall.mp h

lemma eq_zero_of_no_cancel {a b c : k} (_:b ≠ c) (_:a*b = a*c ) : a = 0 := by
  simp_all only [ne_eq, mul_eq_mul_left_iff, false_or]

theorem symm_or_alt_of_reflexive (β:BilinForm k V) ( h : IsRefl β ): 
 IsSymm β ∨ IsAlt β := by
  
  have id₁ (x y z : V) : β x ( (β x y)• z - (β x z) • y ) = 0 := by calc 
    β x ( (β x y)• z - (β x z) • y) = (β x y) * (β x z) - (β x z) * ( β x y) := by simp
                                  _ = 0 := by ring

  have id₂ (x y z : V) : β ((β x y) • z - (β x z) • y) x = 0 := by 
    apply LinearMap.IsRefl.eq_zero h (id₁ x y z)

  have id₃ (x y z : V) : (β x y) * (β z x) = (β x z) * (β y x) := by
    suffices h : (β x y) * (β z x) - (β x z) * (β y x) = 0 by grind
    have : (β ((β x) y • z - (β x) z • y)) x = 0 := id₂ x y z
    rw [ β.sub_left ] at this
    rw [ β.smul_left, β.smul_left ] at this
    exact this

  have id₄ (x y : V) : (β x y)*(β x x) =  (β y x)*(β x x) := by
    rw [ id₃ x y x ] 
    ring
  
  have hs (x y : V) (hx : β x x ≠ 0) : β x y = β y x := by
    apply mul_right_cancel₀ hx 
    exact id₄ x y

   
  by_cases ks:β.IsSymm 
  case pos => exact Or.inl ks
  case neg => 

    apply Or.intro_right

    have hxxyy (x y : V) (h: β x y ≠ β y x) : β x x = 0 ∧ β y y = 0 := by 
      constructor
      case left => sorry
      case right => sorry

    by_contra l

    have hue : ∃ u, β u u ≠ 0 := not_forall.mp l
    rcases hue with ⟨u,hu⟩

    have lvw : ∃ v w, β v w ≠ β w v := not_symm ks
    rcases lvw with ⟨ v, w, hvw ⟩

    have huv : β u v = β v u := by exact hs u v hu
    have huw : β u w = β w u:= by exact hs u w hu 

    have hvw₂ : (β v w) * (β u v) = (β v u) * (β w v) := id₃ _ _ _
    have hvw₃ : (β w v) * (β u w) = (β w u) * (β v w) := id₃ _ _ _    

    rw [ huv, mul_comm ] at hvw₂ 
    rw [ huw, mul_comm ] at hvw₃
        
    have hv₁ : β v u = 0 := by apply eq_zero_of_no_cancel hvw hvw₂

    have hv₂ : β w u = 0 := by apply eq_zero_of_no_cancel hvw.symm hvw₃ 

    have : β (u+v) w ≠ f (u+v w)
    
lemma grove_lemma (β:BilinForm k V) (h:∀ u v w : V, (β u v)*(β w u) = (β v u)*(β u w)) :
  IsSymm β ∨ IsAlt β := by
 
    have : (β u v)*()

    by_cases ks:β.IsSymm 
    case pos => exact Or.inl ks
    case neg =>  
    
    
--------------------------------------------------------------------------------
    
example (h: ¬ ∀ x y:V, β x y = β y x) : ∃ x y:V, β x y ≠ β y x := by
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
