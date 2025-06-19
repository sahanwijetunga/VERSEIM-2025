
import Mathlib.Tactic


-- Let's make some comments about the type `Fin n`

-- if `i:Fin n` then `i.succ:Fin (n+1)`

variable (i:Fin n) in
#check i.succ 

-- but `i.succ` is not the same as `i.castSucc`
-- for example 

example : (Fin.ofNat 3 0) = (Fin.ofNat 2 0).castSucc := by rfl
example : (Fin.ofNat 3 1) = (Fin.ofNat 3 0).succ := by rfl

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

-- so we should be done! That is what `inductionOn` allows.


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
    induction i using Fin.inductionOn 
    
