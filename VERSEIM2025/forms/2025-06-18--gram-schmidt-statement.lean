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

def PosDef (V : Type) [AddCommGroup V] [Module ℝ V] (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ) : Prop :=
  ∀ x : V, β x x ≥ 0 ∧ x ≠ 0 → β x x > 0

def OrthogBasis (V : Type) [AddCommGroup V] [ Module ℝ V] (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
  (c:Basis I ℝ V) : Prop := ∀ (i j : I), i ≠ j → β (c i) (c j) = 0

def orthogonalize_by_gram_schmidt {V:ℕ → Type} [∀ m:ℕ , AddCommGroup (V m)] 
  [∀ m:ℕ, Module ℝ (V m)] (β:(m:ℕ) → V m →ₗ[ℝ] V m →ₗ[ℝ] ℝ) 
  (hp: ∀ m, PosDef (V m) (β m))
  (b:(m:ℕ) → Basis (Fin m) ℝ (V m)) 
  (n:ℕ) :
  Fin n → V n := by
  induction (n:ℕ) with 
  | zero => exact 0
  | succ => exact fun i => 
    if i ≤ n 
