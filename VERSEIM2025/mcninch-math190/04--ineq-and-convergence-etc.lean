/-
Copyright (c) 2024 George McNinch. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Author : George McNinch
-/

/-
course: Math 190 - Tufts University
instructor: George McNinch
semester: 2024 Spring
-/

import Mathlib.Tactic

----------------------------------------------------------------------------------
-- 04 -- Inequalities and convergence
----------------------------------------------------------------------------------

-- inequalities

-- Lean has a notion of inequality of real numbers:

section
variable (x y z : ℝ)

#check x < y
#check x ≤ y


example : x ≤ x := le_refl _

example : x < x → x ≤ x := by
  intro _
  linarith

example : x < y → y < z → x < z := by 
  intro h1 h2
  exact lt_trans h1 h2

example : x < y → y ≤ z → x < z := by
  intro _ _
  linarith

end

-- let's consider a *theorem* about inequalities


theorem my_lemma : ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  sorry 
  done

section

variable (a b δ : ℝ)
variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)

#check my_lemma
#check my_lemma h₀ h₁
#check my_lemma h₀ h₁ ha hb

end


-- we are going to *prove* this statement. Here are some suggested proof terms that we can use!

#check mul_le_mul
#check abs_mul
#check mul_lt_mul_right
#check abs_nonneg

-- we are going to use the `calc` tactic, which is basically a way to
-- connect a sequence of equalities and inequalities.

-- here is the proof skeleton; we are just going to replace the `sorry`s.

example : { x y ε : ℝ } → 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε h₀ h₁ hx hy
  calc
    |x * y| = |x| * |y| := by sorry
    _ ≤ |x| * ε := by sorry
    _ < 1 * ε := by sorry
    _ = ε := by sorry 
  done


example : { x y ε : ℝ } → 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε h₀ h₁ hx hy
  calc
    |x * y| = |x| * |y| := abs_mul _ _
    _ ≤ |x| * ε := by 
         apply mul_le_mul 
         rfl
         linarith
         apply abs_nonneg
         apply abs_nonneg
    _ < 1 * ε := by 
         apply (mul_lt_mul_right h₀).mpr
         linarith
    _ = ε := by ring -- one_mul ε 
  done


-- we could have avoided the `calc` tactic

example : { x y ε : ℝ } → 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε h₀ h₁ hx hy
  rw [ abs_mul x y]
  rw [ ←one_mul ε]
  have _ : |x| * |y| ≤ |x| * ε := by 
      apply mul_le_mul
      rfl
      linarith
      apply abs_nonneg
      apply abs_nonneg
      done
  have _ : |x| * ε < 1 * ε := by 
      apply (mul_lt_mul_right h₀).mpr
      linarith
      done
  linarith
  done


-- # Sequences

-- for a type `α`, a sequence of `α`'s just means a function `s:ℕ → α`.
-- Thus a sequence of real numbers is a function `s:ℕ → ℝ`.

def ConvergesTo (s:ℕ → ℝ) (b:ℝ) := 
  ∀ ε > 0, ∃ N:ℕ, ∀ n ≥ N, |s n - b| < ε

-- note that `∀ ε > 0, ...` is short hand for `∀ ε:ℝ, ε > 0 → ...`

-- also observe that `ConvergesTo` is a `Prop`:

#check ConvergesTo

-- we are going to discuss proofs of convergence

-- we require a new tactic, `congr`

-- it allows us to prove an equation between two expressions by
-- reconciling the parts that are different:

example (a : ℝ) (f:ℝ → ℝ) : f (2*a) = f (3*a - a) := by
  congr 
  ring


-- Finally, the `convert` tactic is used to apply a theorem to a goal
-- when the conclusion of the theorem doesn’t quite match

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_right _).mpr h 
  rw [one_mul] 
  linarith
  --exact lt_trans zero_lt_one h

theorem convergesTo_add 
    {s t : ℕ → ℝ} {a b : ℝ}
    (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  sorry

theorem convergesTo_add' 
   {s t : ℕ → ℝ} {a b : ℝ}
   (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := 
  by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε/2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε/2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n hn
  have hnt : Nt ≤ n := by
    have _ : Nt ≤ max Ns Nt := le_max_right _ _
    linarith
    done
  have hns : Ns ≤ n := by
    have _ : Ns ≤ max Ns Nt := le_max_left _ _
    linarith
    done
  have h₁: |s n - a| < ε/2 := hs n hns
  have h₂: |t n - b| < ε/2 := ht n hnt
  have hst : |s n + t n - (a + b)| ≤ |s n - a| + |t n - b| := by 
    have hh : |s n + t n - (a + b)| = |(s n - a) + (t n - b)| := by 
      congr
      ring
    rw [hh]
    exact abs_add _ _      -- triangle inequality
  have he : |s n - a| + |t n - b| < ε := by
    have _ : |s n - a| + |t n - b| < (ε/2) + (ε/2) := add_lt_add h₁ h₂
    linarith
    done
  linarith
  done


-- #check cauchy
