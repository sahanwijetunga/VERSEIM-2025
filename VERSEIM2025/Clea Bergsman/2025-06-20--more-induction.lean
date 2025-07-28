--------------------------------------------------------------------------------
/-
Copyright (c) 2025 George McNinch. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Clea Bergsman, Katherine Buesing, George McNinch, Sahan Wijetunga
-/

/- VERSEIM-2025 REU -/

import Mathlib.Tactic

--------------------------------------------------------------------------------

-- first, a notation question

structure foo  where
  a : ℝ
  b : ℝ
  hyp : a < b

#check foo.mk 0 1 (by linarith)

#check { a:=0, b:=1, hyp := by linarith : foo }


-- let's prove some statements about factorials.
-- we'll first define them

@[simp]
def fac (n:ℕ) : ℕ :=
  match n with
   | 0 => 1
   | m+1 => (m+1)*fac m

-- we can also define binomial coefficients, though since in the end
-- they are natural numbers, defining them as rationals isn't optimal

def binom (n m :ℕ) : ℚ :=
  fac n / (fac m * fac (n-m))

-- warning! the difference operation on ℕ is funny.
-- e.g.

example :  3 - 5 = (0:ℕ) := rfl

#eval binom 50 3

-- let's give some induction proofs

example (n:ℕ) : n+1 ∣ fac (n+1) := by
  induction n with
  -- now we get two goals. The first is the base case for the
  -- induction:

  | zero => rfl

  -- and the second is the induction step notice that we get the
  -- induction hypothesis in the context - namely that (n+1) ∣ fac (n+1)
  -- - and we must show that (n+2) ∣ fac (n+2)

  | succ n ih =>
    use fac (n+1)
    rfl

-- notice that we didn't even use the induction hypothesis `ih` in
-- that proof


-- here is a more precise version of this result

theorem factorial_fac (n:ℕ) : fac (n+1) = (n+1)*fac n := by
  induction n with
   | zero => rfl
   | succ n ih =>
      rw [ih]
      rfl

-- and a slightly more complicated result...

example (n:ℕ) : fac (n+2) = (n+2)*(n+1)*fac n  := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [ factorial_fac (n+2) ]
      rw [ factorial_fac (n+1) ]
      ring

-- the previous statement seems unsatisfying because it tasks the user
-- with "keeping tracking of the shift in n". On the other hand, that
-- shift is necessary e.g. since

-- `fac 1` is not equal to `1 * 0 * fac (-1)`

-- what about starting induction at a non-zero natural number?

-- the relevant theorem (induction principle) in Mathlib.Data.Nat.Init
-- is named `Nat.le_induction`

example : (n :ℕ) → (nge3 : 3 ≤ n) → 6 ≤ 2*n :=  by
  apply Nat.le_induction
  · norm_num
  · intro n _ _
    linarith

-- we are able to use the `induction` tactic for this case too -- we
-- just have to tell it to use the right "induction princple"

example (n:ℕ) (nge3 : 3 ≤ n) : 6 ≤ 2*n :=  by
  induction n, nge3 using Nat.le_induction with
   | base => norm_num
   | succ => linarith

-- let's get an unshifted version of factorial_fac

theorem factorial_fac' (n:ℕ) (nge1 : 1 ≤ n) : fac n = n*fac (n-1) := by
  induction n, nge1 using Nat.le_induction with
  | base => norm_num
  | succ => rfl


-- and another factorization result

theorem factorial_fac_2 (n:ℕ) {nge2:2 ≤ n} : fac n = n * (n-1) * fac (n-2) := by
  induction n, nge2 using Nat.le_induction  with
  | base =>  norm_num
  | succ m h a =>
        rw [ factorial_fac' m (by linarith) ] at a
        simp
        rw [ factorial_fac' m (by linarith) ]
        ring


-- let's prove that factorial is always positive (!)

theorem factorial_pos (n:ℕ) : fac n > 0 := by
  induction n with
  | zero => norm_num
  | succ n ih => unfold fac
                 apply mul_pos
                 · linarith
                 · exact ih

-- in particular, it is non-zero

theorem factorial_ne_zero (n:ℕ) : fac n ≠ 0 := by
  have : fac n > 0 := factorial_pos n
  linarith

-- we can prove some computations

theorem fac_two : fac 2 = 2 := by
  norm_num

theorem fac_three : fac 3 = 6 := by
  norm_num

theorem fac_five : fac 5 = 120 := by
  norm_num


-- now let's describe the the binomial coefficient `binom n 2`  for `2 ≤ n`

theorem choose_2  (n:ℕ) (nge2 : 2 ≤ n):  binom n 2 = n*(n-1)/2 := by
  unfold binom
  rw [ @factorial_fac_2 n nge2  ]
  have h : fac (n-2) ≠ 0 := factorial_ne_zero _
  rw [fac_two ]
  field_simp     -- (!!)
  ring

-- notice that the `field_simp` tactic requires the is only able/willing to cancel
-- the `fac (n-2)` factor of the numberator & denominator of an expression in ℚ
-- with a proof of that factor is non-zero

-- e.g. the following doesn't work without the "non-zero" hypothesis.

example (a b : ℚ) (_:b≠ 0)
   : a*b/b = a := by field_simp

-- exercise!

example  (n m:ℕ) (hmn : m ≤ n) : fac m ∣ fac n := by sorry





--------------------------------------------------------------------------------

-- induction and `Fin n`


-- Let's make some comments about the type `Fin n`

-- if `i:Fin n` then `i.succ:Fin (n+1)`

variable (i:Fin n) in
#check i.succ

-- but `i.succ` is not the same as `i.castSucc`
-- for example

example : (Fin.ofNat 3 0) = (Fin.ofNat 2 0).castSucc := by rfl
example : (Fin.ofNat 3 1) = (Fin.ofNat 2 0).succ := by rfl

-- Let's understand how `Fin.inductionOn` works.

-- the idea is that you have some parametrized `Prop`s that you
-- want to prove.  The docs tend to call this the `motive`, like

-- variable (motive: Fin (n+1) → Prop)

-- so you want to prove `motive i` for each `i : Fin (n+1)`

-- Of course, we look at `Fin (n+1)` since `Fin 0` is *empty*!

-- so for a given `n:ℕ` we want to prove `motive i` for each `i:Fin (n+1)`

-- and `inductionOn` permits us to prove this by induction on the
-- underlying natural number (n:ℕ)

-- We need two things:

-- 1. the base case, namely a proof of `motive 0`

-- 2. a successor step, formulated like this:

-- succ: (i:Fin n) → motive i.castSucc → motive i.succ

-- in our notation, notice that

-- `i.castSucc : Fin (n+1)` and `i.succ : Fin (n+1)`

-- which is good because we have only formulated `motive` as a
-- function on `Fin (n+1)`.

-- so the idea is that we suppose we know how to prove
-- "result for i implies the result for (i+1)" for each i=0,1,...n

-- and we suppose we know how to prove the result for i =0.

-- so we should be done! That is what `Fin.inductionOn` allows.


example (n:ℕ)
  (motive: Fin (n+1) → Prop)
  (h0 : motive 0)
  (hsucc : (j:Fin n) → motive j.castSucc → motive j.succ)
  : ∀ i, motive i :=  by
    intro i
    apply Fin.inductionOn
    · exact h0
    · exact hsucc


-- we can actually use the `induction` tactic to apply this result for
-- us:

example (n:ℕ)
  (motive: Fin (n+1) → Prop)
  (h0 : motive 0)
  (hsucc : (j:Fin n) → motive j.castSucc → motive j.succ)
  : ∀ i, motive i :=  by
    intro i
    induction i using Fin.inductionOn with
     | zero => exact h0
     | succ i ih => exact hsucc i ih
