import Mathlib.Tactic

-- for a finite dimensional ℝ-vector space V with a positive definite
-- bilinear form, the Gram-Schmidt process takes as input a (random)
-- basis of V and returns an orthogonal basis for V.

-- to capture the algorithmic nature of this, let's write a function that
-- produces the new candidate basis -- the return value of the function will be
-- a function `Fin n → V`.

-- we'll have to check that this function is `LinearIndepent` and
-- hence determines a basis, and then check that this basis satisfies
-- `OrthogBasis`

def PosDef {V : Type} [AddCommGroup V] [Module ℝ V] (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ) : Prop :=
  ∀ x : V, β x x ≥ 0 ∧ x ≠ 0 → β x x > 0

def OrthogBasis {V : Type} [AddCommGroup V] [ Module ℝ V ] (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
  (c:Basis I ℝ V) : Prop := ∀ (i j : I), i ≠ j → β (c i) (c j) = 0

def orthog_by_gs {V:Type} [AddCommGroup V] [Module ℝ V] 
  (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hp : PosDef β)
  {m:ℕ}
  (b:Fin m → V) (hb : LinearIndependent ℝ b)
  : Fin m → V := match m with 
   | Nat.zero => b
   | Nat.succ m => by sorry


def restrict {m:ℕ} (f:Fin (m+1) → ℕ) : Fin m → ℕ :=
  fun i => f i.castSucc 


def extend {m:ℕ} (f:Fin m → ℕ) (x :ℕ) : Fin (m+1) → ℕ :=
  fun i =>
  if h:i ≠ Fin.last m then f (i.castPred h) else x

#eval restrict ![2,3,4,5,8]

#eval extend ![1,1,1] 2
  
  
