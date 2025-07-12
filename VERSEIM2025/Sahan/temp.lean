import Mathlib.Tactic

open Real

-- We tell `grind` that whenever it sees `cos x` or `sin x`,
-- it should add `(cos x)^2 + (sin x)^2 = 1` to the whiteboard.
grind_pattern cos_sq_add_sin_sq => sin x

-- Here `grind` notices that `(cos x)^2 + (sin x)^2 = 1`,
-- sends this to the Grobner basis module,
-- and we can prove equalities modulo that relation!
example : (cos x + sin x)^2 = 2 * cos x * sin x + 1 := by grind

-- `grind` notices that the two arguments of `f` are equal,
-- and hence the function applications are too.
example (f : ℝ → ℕ) : f ((cos x + sin x)^2) = f (2 * cos x * sin x + 1) := by grind

-- After that, we can use basic modularity conditions:
-- this reduces to `4 * x ≠ 2 + x` for some `x : ℕ`
example (f : ℝ → ℕ) : 4 * f ((cos x + sin x)^2) ≠ 2 + f (2 * cos x * sin x + 1) := by
  grind

-- A bit of case splitting is also fine.
-- If `max = 3`, then `f _ = 0`, and we're done.
-- Otherwise, the previous argument applies.

variable {k V: Type} [Field k][AddCommGroup V][Module k V]

example {I: Type} (i j: I) (W: I → Submodule k V) (h: i=j) (wi: W i) (wj: W j): True := by
  have: W i = W j := sorry
  have: wi = h ▸ wj := by
    congr
    sorry
  sorry
