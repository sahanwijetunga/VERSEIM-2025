
# ideas

- introduce notation for `equiv_of_spaces_with_form`

  ```
  notation:100 lhs:100 "["lhb:100"]≃["rhb:100"]" rhs:100 => equiv_of_spaces_with_form (V₁ := lhs) (V₂ := rhs) lhb rhb
  ```
  
  After this declaration, the type
  
  ```
  V₁ [β₁]≃[β₂] V₂
  ```
  
  should mean the same thing as
  
  ```
  equiv_of_spaces_with_form β₁ β₂
  ```
  
- prove results:

  ```
  def anisotropic {V : Type} [ AddCommGroup V ] [ Module k V ] 
    (β:BilinForm k V) (v:V) : Prop := β v v ≠ 0

  def anisotropicVector {V : Type} [ AddCommGroup V ] [ Module k V ] 
    (β:BilinForm k V) (v:V) : Prop := β v v ≠ 0

  def anisotropic {V : Type} [ AddCommGroup V ] [ Module k V ] 
    (β:BilinForm k V) : Prop := ∀ v, v ≠ 0 → anisotropicVector β v

  example (eq : V₁ [β₁]≃[β₂] V₂) (han : anisotropic β₁) 
  
