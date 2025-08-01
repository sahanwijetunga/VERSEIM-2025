-- noncomputable example: F[X] →ₗ[F] F(X) := by
--   -- have h1: F[X] →ₗ[F[X]] F(X) := Algebra.linearMap F[X] (F(X))
--   -- have h2: F[X] →+* F(X) := algebraMap F[X] F(X)
--   exact AlgHom.toLinearMap (Algebra.algHom F F[X] F(X))


-- example: (TensorProduct.AlgebraTensorModule.map (Algebra.linearMap F[X] (F(X))) LinearMap.id: V[F] → V(F))
--    = TensorProduct.map (AlgHom.toLinearMap (Algebra.algHom F F[X] F(X))) LinearMap.id := by
--    rfl

-- example: Function.Injective ⇑(Algebra.algHom F F[X] F(X)).toLinearMap := by
--   have: (⇑(Algebra.algHom F F[X] F(X)).toLinearMap: F[X] → F(X))
--     = Algebra.algHom F F[X] F(X) := rfl
--   rw[this]
--   have: (Algebra.algHom F F[X] F(X) : F[X] → F(X)) = algebraMap F[X] F(X) := rfl
--   rw[this]
--   exact RatFunc.algebraMap_injective F
