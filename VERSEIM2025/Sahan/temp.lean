-- import Mathlib.Algebra.Module.LinearMap.Basic
-- import Mathlib.Tactic

-- variable {k : Type*} [Field k]
-- variable {V W : Type*} [AddCommGroup V] [Module k V]
-- variable [AddCommGroup W] [Module k W]

-- def myFunc (x : V) : W := sorry -- your function here


-- def myLinearMap (hf_add : ∀ x y : V, myFunc (x + y) = ((myFunc x) + (myFunc y): W))
--     (hf_smul : ∀ (c : k) (x : V), myFunc (c • x) = ((c • myFunc x): W)): V →ₗ[k] W where
