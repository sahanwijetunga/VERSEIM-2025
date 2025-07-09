
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

example {m n :ℕ} (M:Matrix (Fin m) (Fin n) k) : stdVS k n →ₗ[k] stdVS k m := 
  Matrix.toLin (sbv n) (sbv m) M

-- now the null space of the matrix is precise the kernel of this
-- linear transformation.

-- and the nullity of M is just the dimension of this null space

-- we *could* treat it as a natural number (ℕ), but some results we
-- seem to need are stated in terms of the type `Cardinal`, so we'll
-- use that.

def Nullity (M:Matrix (Fin m) (Fin n) k) : Cardinal :=
  let null_space : Submodule k (stdVS k n) := 
    LinearMap.ker (Matrix.toLin (sbv n) (sbv m) M)
  Module.rank k null_space    

-- The rank of the matrix is precisely the dimension of the image of
-- the corresponding linear transformation. This is the "column
-- space" -- i.e. the span of the columns of M, viewed as vectors in
-- `stdVS k m`.

-- lWe can compare `LinearMap.rank` with `Matrix.rank`
   
-- the main point is that the column space of a matrix identifies with
-- the image of the corresponding linear map k^n → k^n.
 
lemma mulVecLin_eq_toLin_sbv (M:Matrix (Fin m) (Fin n) k) : 
   M.mulVecLin = Matrix.toLin (sbv n) (sbv m) M := by
   rfl 

lemma rank_eq_linmap_rank  {m n :ℕ} (M:Matrix (Fin m) (Fin n) k) : 
   (M.rank:Cardinal)  = LinearMap.rank (Matrix.toLin (sbv n) (sbv m) M) := by 
   unfold Matrix.rank 
   rw [ mulVecLin_eq_toLin_sbv M ]
   simp 

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
  M.rank + Nullity M = n := by
  unfold Nullity
  rw [ rank_eq_linmap_rank ]
  rw [ LinearMap.rank_range_add_rank_ker (Matrix.toLin (sbv n) (sbv m) M) ]
  exact rank_fin_fun n

-- in the next proof, we use the quotient construction on vector
-- spaces and instead use `LinearMap.rank_quotient_add_rank`

theorem quotient_dim  ( V : Type )
  [ AddCommGroup V] [ Module k V] 
  (W : Submodule k V) [FiniteDimensional k V]
  : Module.rank k (V ⧸ W) + Module.rank k W = Module.rank k V  := by 
  apply Submodule.rank_quotient_add_rank


theorem rank_nullity' (M:Matrix (Fin m) (Fin n) k) : 
  M.rank + Nullity M = n := by
  let linmap : stdVS k n →ₗ[k] stdVS k m := Matrix.toLin (sbv n) (sbv m) M
  unfold Nullity
  have linear_equiv : LinearMap.range (Matrix.toLin (sbv n) (sbv m) M) 
                ≃ₗ[k] (stdVS k n) ⧸ (LinearMap.ker linmap) := 
    (LinearMap.quotKerEquivRange (Matrix.toLin (sbv n) (sbv m) M)).symm  
  have dim_eq : Module.rank k ↥(LinearMap.range linmap) = 
                Module.rank k (stdVS k n ⧸ LinearMap.ker linmap) := 
   LinearEquiv.rank_eq linear_equiv
  rw [ rank_eq_linmap_rank M] 
  rw [ LinearMap.rank_range_add_rank_ker linmap ]
  exact rank_fin_fun n

--------------------------------------------------------------------------------

-- the "invertible matrix theorem" results which give the main results over fields are

-- `LinearMap.isUnit_iff_range_eq_top` and
-- `LinearMap.isUnit_iff_ker_eq_bot`

theorem matrix_fullrank_iff_det_ne_zero (n:ℕ) (M:Matrix (Fin n) (Fin n) k) 
  : M.det ≠ 0 ↔ M.rank = (n:Cardinal) := by
  constructor
  · intro hdet
    have im : IsUnit M := by 
      apply (Matrix.isUnit_iff_isUnit_det M).mpr
      simp
      exact hdet
    rw [ Matrix.rank_of_isUnit M im ]
    simp
  · intro h

    let linmap : stdVS k n →ₗ[k] stdVS k n := M.mulVecLin -- Matrix.toLin (sbv n) (sbv n) M
    --    rw [ rank_eq_linmap_rank M ] at h
    
    apply (Matrix.isUnit_iff_isUnit_det M).mp 

    apply (LinearMap.isUnit_iff_range_eq_top linmap).mpr ?_


example (n m :ℕ) (f:stdVS k n →ₗ[k] stdVS k n)  (finv : LinearMap.ker f = ⊥) :
  IsUnit f := by exact (LinearMap.isUnit_iff_ker_eq_bot f).mpr finv



  





