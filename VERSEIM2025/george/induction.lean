
import Mathlib.Tactic

-- let's prove "from scratch" that the binomial coefficients are Natural numbers

-- we'll first define factorials

@[simp]
def fac (n:ℕ) : ℕ :=
  match n with
   | 0 => 1
   | m+1 => (m+1)*fac m

def binom (n m :ℕ) : ℚ :=
  fac n / (fac m * fac (n-m))

-- warning! the difference operation on ℕ is funny.
-- e.g. 

example :  3 - 5 = (0:ℕ) := rfl

#eval binom 50 2 


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

-- notice that we didn't even use the `ih` in that proof


-- here is a more precise version of this result

theorem factorial_fac (n:ℕ) : fac (n+1) = (n+1)*fac n := by
  induction n with
   | zero => rfl
   | succ n ih => 
      rw [ih]
      rfl

-- and a more complicated result...        
     
example (n:ℕ) : (n+2)*(n+1)*fac n =  fac (n+2) := by
  induction n with 
  | zero => rfl       
  | succ n ih => 
      rw [ factorial_fac (n+2) ]
      rw [ factorial_fac (n+1) ]
      ring

-- what about starting induction at a non-zero natural number?

-- the relevant theorem (induction principle) in Mathlib.Data.Nat.Init
-- is Nat.le_induction

example : (n:ℕ) → (nge2 : 1 ≤ n) → n > 0 :=  by
  apply Nat.le_induction 
  · norm_num
  · intro n pos 
    norm_num


-- we should be able to use the induction tactic -- we just have to
-- tell it to use the right "induction princple"

example (n:ℕ) (nge2 : 1 ≤ n) : n > 0 :=  by
  induction n, nge2 using Nat.le_induction with
   | base => norm_num
   | succ => norm_num

-- let's get a restated version of factorial_fac

theorem factorial_fac' (n:ℕ) (nge2 : 2 ≤ n) : fac n = n*fac (n-1) := by
  induction n, nge2 using Nat.le_induction with
  | base => norm_num
  | succ => rfl


-- let's state an equality in ℚ (for reasons that will be more clear below)
--
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

example (n:ℕ) : fac n ≠ 0 := by 
  have : fac n > 0 := factorial_pos n
  linarith


theorem fac_two : fac 2 = 2 := by
  norm_num

theorem fac_three : fac 3 = 6 := by
  norm_num

theorem fac_five : fac 5 = 120 := by
  norm_num

