
import Mathlib.Tactic
import Mathlib.Data.Matrix.Rank


-- let's prove for an m×n matrix that rank + nullity = n.

noncomputable section

variable { k : Type } [Field k]

-- let's introduce the "standard" k  vector space

abbrev stdVS  (k:Type) [Field k] (n:ℕ) : Type := (Fin n → k)

-- we use `abbrev` so that Lean is (more likely to) automatically
-- unfolds the definition -- this really is mainly an abbreviation to
-- avoid typing the pesky arrow `→`

example (n:ℕ) : Module k (stdVS k n) := inferInstance

-- let's write `sbv n` for the standard basis of `stdVS k n`.
  
abbrev sbv (n:ℕ) : Basis (Fin n) k (stdVS k n) := Pi.basisFun k (Fin n)

-- given an m × n matrix M, and using the standard bases, we get a
-- corresponding linear transformation

-- `stdVS n ---> stdVS m` using `Matrix.toLin`

def map_of_matrix {m n :ℕ} (M:Matrix (Fin m) (Fin n) k) : stdVS k n →ₗ[k] stdVS k m := 
  Matrix.toLin (sbv n) (sbv m) M

-- now the null space of the matrix is precise the kernel of this
-- linear transformation.

-- and the nullity of M is just the dimension of this null space

-- we *could* treat it as a natural number (ℕ), but some results we
-- seem to need are stated in terms of the type `Cardinal`, so we'll
-- use that.

def Nullity (M:Matrix (Fin m) (Fin n) k) : Cardinal :=
  let null_space : Submodule k (stdVS k n) := LinearMap.ker (map_of_matrix M)
  Module.rank k null_space    

-- The rank of the matrix is precisely the dimension of the image of
-- the corresponding linear transformation. (This is the "column
-- space" -- i.e. the span of the columns of M, viewed as vectors in
-- `stdVS k m`.


def Rank (M:Matrix (Fin m) (Fin n) k) : Cardinal := 
  let linmap : stdVS k n →ₗ[k] stdVS k m := map_of_matrix M
  let image : Submodule k (stdVS k m) := LinearMap.range linmap
  Module.rank k image

    
    


-- this is actually already implemented in Mathlib, as `LinearMap.rank`,
-- and it coincides with the definition we just gave.

example (M:Matrix (Fin m) (Fin n) k) : 
   Rank M  = LinearMap.rank (map_of_matrix M) := by 
   unfold Rank
   unfold LinearMap.rank
   rfl

-- and it also coincides with `Matrix.rank`


example (M:Matrix (Fin m) (Fin n) k) : 
   M.rank = LinearMap.rank (map_of_matrix M) := by 
   unfold Matrix.rank
   unfold map_of_matrix
      


-- --------------------------------------------------------------------------------
-- 
-- now the rank-nullity theory compares these numbers!

-- the main extra thing to know is this: the mapping

-- `φ_M : stdVS k n ---> stdVS k m` determined by M induces an invertible
-- linear mapping from the quotient space `stdVS k n ⧸ Null M` to the
-- image (in `stdVS k m`) of φ_M.

-- moreover, for any finite dimensional vector space `V` and any
-- subspace `W : Submodule k V` the quotient space `V ⧸ W` has dimension
-- `dim V ⧸ W = dim V - dim W`.

-- This means that the dimension of the image of φ is equal to 
-- `dim stdVS k n - Nullity M` -- i.e. `n - Nullity M` 


--  the invertible linear mapping between `stdVS k n ⧸ Null M` and the
--  image of `φ_M` follows from `LinearMap.quotKerEquivRange`

-- This amounts to the rank-nullity theorem!

example (l:ℕ) : Module.rank k (Fin l → k) = l := by exact rank_fin_fun l 

-- in the next proof, the real work is done by
-- `LinearMap.rank_range_add_rank_ker`

theorem rank_nullity (M:Matrix (Fin m) (Fin n) k) : 
  Rank M + Nullity M = n := by
  unfold Rank
  unfold Nullity
  rw [ LinearMap.rank_range_add_rank_ker (map_of_matrix M) ]
  exact rank_fin_fun n

-- in the next proof, we use the quotient construction on vector
-- spaces and instead use `LinearMap.rank_range_add_rank_ker`

theorem quotient_dim  ( V : Type )
  [ AddCommGroup V] [ Module k V] 
  (W : Submodule k V) [FiniteDimensional k V]
  : Module.rank k (V ⧸ W) + Module.rank k W = Module.rank k V  := by 
  apply Submodule.rank_quotient_add_rank


theorem rank_nullity' (M:Matrix (Fin m) (Fin n) k) : 
  Rank M + Nullity M = n := by
  unfold Rank
  unfold Nullity
  have linear_equiv : LinearMap.range (map_of_matrix M) ≃ₗ[k] (stdVS k n) ⧸ LinearMap.ker (map_of_matrix M) := 
    (LinearMap.quotKerEquivRange (map_of_matrix M)).symm  
  have dim_eq : Module.rank k ↥(LinearMap.range (map_of_matrix M)) = 
                Module.rank k (stdVS k n ⧸ LinearMap.ker (map_of_matrix M)) := 
   LinearEquiv.rank_eq linear_equiv
  rw [ LinearMap.rank_range_add_rank_ker (map_of_matrix M) ]
  exact rank_fin_fun n

--------------------------------------------------------------------------------

theorem matrix_fullrank_iff_det_ne_zero (n:ℕ) (M:Matrix (Fin n) (Fin n) k) 
  (hdet : M.det ≠ 0) : M.rank = ↑n := by
  have im : IsUnit M := by 
    apply (Matrix.isUnit_iff_isUnit_det M).mpr
    simp
    exact hdet
  rw [ Matrix.rank_of_isUnit M im ]
  simp
  





