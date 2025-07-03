
import Mathlib.Tactic
import Mathlib.Data.Matrix.Rank


-- let's prove for an m×n matrix that rank + nullity = n.

noncomputable section

variable { k : Type } [Field k]

-- let's introduce the "standard" k  vector space
--abbrev stdVS (k:Type) [Field k] (n:ℕ) : Type := (Fin n →₀ k)
abbrev stdVS  (k:Type) [Field k] (n:ℕ) : Type := (Fin n →₀ k)

-- we use `abbrev` so that Lean automatically unfolds the definition
-- -- this really is justan abbreviation to avoid typing the pesky
-- arrow →₀

example (n:ℕ) : Module k (stdVS k n) := inferInstance

-- let's write `sbv n` for the standard basis of `stdVS k n`.
  
abbrev sbv (n:ℕ) : Basis (Fin n) k (stdVS k n) := Finsupp.basisSingleOne 

-- given an m × n matrix M, and using the standard bases, we get a
-- corresponding linear transformation

-- `stdVS n ---> stdVS m` using `Matrix.toLin`

def map_of_matrix {m n :ℕ} (M:Matrix (Fin m) (Fin n) k) : stdVS k n →ₗ[k] stdVS k m := 
  Matrix.toLin (sbv n) (sbv m) M

-- now the null space of the matrix is precise the kernel of this
-- linear transformation.

-- and the nullity of M is just the dimension of this null space

def Nullity (M:Matrix (Fin m) (Fin n) k) : Cardinal :=
  Module.rank k null_space
  where
    null_space : Submodule k (stdVS k n) := LinearMap.ker (map_of_matrix M)

-- and the rank of the matrix is precisely the dimension of the image
-- of this linear transformation

-- in fact, Lean defines the rank of a linear transformation to be the
-- dimension of its image

-- but `LinearMap.rank` considers the rank to be a `Cardinal`
-- (possibly infinite). In our case, we just expect a natural number.

def Rank (M:Matrix (Fin m) (Fin n) k) : Cardinal := 
  Module.rank k image
  where
    linmap : stdVS k n →ₗ[k] stdVS k m := map_of_matrix M
    image : Submodule k (stdVS k m) := LinearMap.range linmap


-- on the other hand, `Module,finrank_eq_rank` shows the two notions
-- coincide for finite dimensional vector spaces. So the above notion
-- should coincide with the rank defined by Mathlinb:

example (M:Matrix (Fin m) (Fin n) k) : Cardinal := 
   LinearMap.rank linmap
   where
    linmap : stdVS k n →ₗ[k] stdVS k m := map_of_matrix M


example (M:Matrix (Fin m) (Fin n) k) : 
   Rank M  = LinearMap.rank (map_of_matrix M) := by 
   unfold Rank
   unfold Rank.image
   unfold Rank.linmap
   unfold LinearMap.rank
   rfl
--   apply Module.finrank_eq_rank

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

theorem rank_nullity (M:Matrix (Fin m) (Fin n) k) : 
  Rank M + Nullity M = n := by
  unfold Rank
  unfold Rank.image
  unfold Rank.linmap
  unfold Nullity
  unfold Nullity.null_space
  have : LinearMap.range (map_of_matrix M) ≃ (stdVS k n) ⧸ LinearMap.ker (map_of_matrix M) := by
   apply (LinearMap.quotKerEquivRange (map_of_matrix M)).symm 

#check (LinearMap.quotKerEquivRange ?_).symm 

open LinearMap

theorem quotient_dim  ( V : Type )
  [ AddCommGroup V] [ Module k V] 
  (W : Submodule k V) [FiniteDimensional k V]
  : Module.rank k (V ⧸ W) + Module.rank k W = Module.rank k V  := by 
  apply Submodule.rank_quotient_add_rank

