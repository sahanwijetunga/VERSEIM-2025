
import Mathlib.Tactic

-- problem 1.
-- ==========


variable {k : Type} [Field k]

variable {V : Type} [ AddCommGroup V ] [ Module k V ]
variable {W : Type} [ AddCommGroup W ] [ Module k W ]
variable {X : Type} [ AddCommGroup X ] [ Module k X ]

variable {π : V →ₗ[k] W}    
variable {ψ : W →ₗ[k] X}    

open Submodule
open LinearMap

example (hpsi :  ker ψ = ⊥) : ker (ψ ∘ₗ π) = ker π := by 
  ext 
  simp
  sorry

-- problem 2.
-- ==========

example (hpi : map ψ ⊤ = ⊤) : map (ψ ∘ₗ π) ⊤ = (map ψ ⊤ : Submodule k X) := by 
  ext
  simp
  sorry


-- problem 3.
-- ==========


-- lemma add_eq {k:Type} [Field k] {a b c d : k} (h1 : a = b) (h2 : c = d) 
--   : a + c = b + d := by
--   rw [ h1, h2 ] 

lemma zero_iff_two_mul_zero (a:ℚ) : a = 0 ↔ 2*a = 0 := by
  constructor
  repeat intro _ ; linarith

example (a b c : ℚ) : (a•(![1,1,0]:Fin 3 → ℚ) + b•![1,-1,0] + c•![3,2,1] = 0) → 
   (a =0 ∧ b = 0 ∧ c = 0) := by
   norm_num 
   intro h1 h2 h3 _
   rw [h3, zero_mul, add_zero ] at h1
   rw [h3, zero_mul, add_zero ] at h2
   have k1 : a = 0 := by
     rw [ zero_iff_two_mul_zero, two_mul ] 
     calc 
       a + a = a + a + b + -b     := by ring
       _     = (a + b) + (a + -b) := by ring
       _     = 0                  := by rw [h1, h2]; ring
     
   have k2 : b = 0 := by 
     rw [ zero_iff_two_mul_zero, two_mul ]
     calc 
       b + b = a + -a + b + b     := by ring
       _     = (a + b) - (a + -b) := by ring
       _     = 0                  := by rw [h1,h2]; ring
   exact ⟨ k1, k2, h3⟩
   

  
end exercises
