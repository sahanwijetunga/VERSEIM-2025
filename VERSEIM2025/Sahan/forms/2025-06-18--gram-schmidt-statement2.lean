
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

def Def {V : Type} [AddCommGroup V] [Module ℝ V] (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ) : Prop :=
  ∀ x : V, x ≠ 0 → β x x ≠ 0

def PosDef {V : Type} [AddCommGroup V] [Module ℝ V] (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ) : Prop :=
  ∀ x, (β x x ≥ 0 ∧ (x ≠ 0 → β x x > 0))

def Symm {V : Type} [AddCommGroup V] [Module ℝ V] (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ) : Prop :=
  ∀ x y, β x y = β y x

lemma posDef_is_Def {V : Type} [AddCommGroup V] [Module ℝ V] (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (h: PosDef β) : Def β := by
  intro x hx
  suffices β x x > 0 from ?_
  . linarith
  apply (h x).right
  assumption


def OrthogPred {V : Type} [AddCommGroup V] [ Module ℝ V ] (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
  (c: I → V) : Prop := ∀ (i j : I), i ≠ j → β (c i) (c j) = 0


def OrthogBasis {V : Type} [AddCommGroup V] [ Module ℝ V ] (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
  (c:Basis I ℝ V) : Prop := OrthogPred β c

@[ext]
structure OrthogNonZero {V : Type} [AddCommGroup V] [ Module ℝ V ] (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (n: ℕ) where
  toFun: Fin n → V
  orthog: OrthogPred β toFun
  non_zero: (i: Fin n) → toFun i ≠ 0

def restrict {X:Type} {m:ℕ} (f:Fin (m+1) → X) : Fin m → X :=
  fun i => f i.castSucc

noncomputable def proj {V : Type} [AddCommGroup V] [ Module ℝ V ] (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (u v: V) : V :=
  (β v u / β u u) • u

lemma proj_nice  {V : Type} [AddCommGroup V] [ Module ℝ V ] (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (u v w: V)
  (h: β u v = 0): β u (proj β v w) = 0 := by
    unfold proj
    simp[h]

lemma proj_nice'  {V : Type} [AddCommGroup V] [ Module ℝ V ] (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (u v: V)
  (h': β u u ≠ 0): β u (proj β u v) = β v u := by
    unfold proj
    field_simp


example {V : Type} [AddCommGroup V] [ Module ℝ V ] (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ) {n: ℕ} (b: Fin n → V) (v: V):
  β v (∑ i, b i)= ∑ i, β v (b i) := by
    exact LinearMap.BilinForm.sum_right β Finset.univ v b

lemma not_needed_sum_one_nonzero_element {n: ℕ} (l: Fin n → ℝ) (i: Fin n) (h: (j: Fin n) → j ≠ i → l j =0):
  l i = ∑ j, l j := by exact Eq.symm (Fintype.sum_eq_single i h)

lemma restrict_linear_independent {V:Type} [AddCommGroup V] [Module ℝ V]
  {n:ℕ}  (b:Fin (n+1) → V) (hb : LinearIndependent ℝ b) : LinearIndependent ℝ (restrict b) := by
    unfold restrict
    apply LinearIndependent.comp hb Fin.castSucc
    exact Fin.castSucc_injective n

def intermediate {V:Type} [AddCommGroup V] [Module ℝ V]
  (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hp : PosDef β) (hs : Symm β)
  {n:ℕ} (b:Fin n → V)

noncomputable def gram_schmidt {V:Type} [AddCommGroup V] [Module ℝ V]
  (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hp : PosDef β) (hs : Symm β)
  {n:ℕ}
  (b:Fin n → V) (hb : LinearIndependent ℝ b)
  : Fin n → V := match n with
   | Nat.zero =>  (fun _ ↦ 0)
   | Nat.succ n => by
    have hnlessnsucc : n<n+1 := by norm_num
    let b' := restrict b
    have b'_linear_independent: LinearIndependent ℝ b' := restrict_linear_independent b hb
    let c' := gram_schmidt β hp hs b' b'_linear_independent

    let b_last := b ⟨n, hnlessnsucc⟩

    let c_last: V := b_last - ∑ i, proj β (c' i) (b_last)
    let c : Fin (n+1) → V := fun ⟨m, h⟩  =>
      if h' : m ≠ n then c' ⟨m, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h) h'⟩
        else c_last
    exact c



theorem orthog_span_gram_schmidt {V:Type} [AddCommGroup V] [Module ℝ V]
  (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hp : PosDef β) (hs : Symm β)
  {n:ℕ}
  (b:Fin n → V)
  : (OrthogPred β (gram_schmidt β hp hs b hb)) ∧
    (Submodule.span ℝ (Set.range b)=Submodule.span ℝ (Set.range (gram_schmidt β hp hs b hb))) :=
  match n with
  | Nat.zero => by
    constructor
    . intro i j h
      have: ↑i<(0: ℕ) := by exact i.isLt
      linarith
    . exact linearIndependent_empty_type
  | Nat.succ n => by
    let c := gram_schmidt β hp hs b hb
    have orthog: OrthogPred β c := sorry
    have linearindependent: Orthog
    simp[gram_schmidt]

    sorry


#eval restrict ![2,(3: ℚ ),(4: ℕ),5,8]

def extend {X:Type} {m:ℕ} (f:Fin m → X) (x :X) : Fin (m+1) → X :=
  fun i =>
  if h:i ≠ Fin.last m then f (i.castPred h) else x

#eval restrict ![2,3,4,5,8]

#eval extend ![1,1,1] 2



-- let's write a function which takes as argument
-- a vector-values function w and returns the function
-- whose value at i is `w i` minus the sum of all the `w j` for `j < i`.

-- we can write this "recursively" as follows:

def construct {V:Type} [AddCommGroup V] [Module ℚ V] {m:ℕ} (w:Fin (m+1) → V)
  : Fin (m+1) → V :=
  match m with
   | 0 => w
   | m+1 => by
    have prior: Fin (m+1) -> V := construct (restrict w)
    have new_term: V := (w (Fin.last (m+1)) - (∑ j : Fin (m+1), w j.castSucc))
    exact extend prior new_term


def sbv (n:ℕ) : Fin n → Fin n → ℚ := by
  intro i
  exact Pi.single i (1:ℚ)


#eval construct (sbv 5)
