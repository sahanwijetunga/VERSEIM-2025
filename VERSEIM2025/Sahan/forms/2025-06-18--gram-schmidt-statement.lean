
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

def orthog_by_gs {V:Type} [AddCommGroup V] [Module ℝ V]
  (β:V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hp : PosDef β) (hs : Symm β)
  {n:ℕ}
  (b:Fin n → V) (hb : LinearIndependent ℝ b)
  : OrthogNonZero β n := match n with
   | Nat.zero =>  ⟨fun _ ↦ 0, by
    unfold OrthogPred
    rintro a b h
    simp, by
      intro i
      exfalso
      have: i<(0: ℕ) := by exact i.isLt
      simp_all
      ⟩
   | Nat.succ n => by
    have hnlessnsucc : n<n+1 := by norm_num
    let b' := restrict b
    have b'_linear_independent: LinearIndependent ℝ b' := restrict_linear_independent b hb
    let c' := orthog_by_gs β hp hs b' b'_linear_independent

    let b_last := b ⟨n, hnlessnsucc⟩

    let c_last: V := b_last - ∑ i, proj β (c'.toFun i) (b_last)

    have c_orthog_rest_last: (i: Fin n) → β (c'.toFun i) c_last=0 := by
      intro i
      rw[map_sub]
      suffices β (c'.toFun i) (b_last) = β (c'.toFun i) (∑ j, proj β (c'.toFun j) b_last) from ?_
      . rw[this, sub_self]

      -- have: β (c'.toFun i) (∑ j, proj β (c'.toFun j) (b ⟨n, by norm_num⟩))= from ?_
      rw[LinearMap.BilinForm.sum_right]
      show (β (c'.toFun i)) (b_last)=∑ j, (β (c'.toFun i)) (proj β (c'.toFun j) b_last)

      have orthog_i_j (j: Fin n): (j ≠ i) → (β (c'.toFun i)) (proj β (c'.toFun j) b_last)=0 := by
        intro h
        apply proj_nice
        apply c'.orthog
        tauto
      rw[Fintype.sum_eq_single i orthog_i_j]
      rw[proj_nice' β _ _ ((posDef_is_Def β hp) (c'.toFun i) (c'.non_zero i))]
      apply hs

    let c : Fin (n+1) → V := fun ⟨m, h⟩  =>
      if h' : m ≠ n then c'.toFun ⟨m, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h) h'⟩
        else c_last

    have hc_last: c_last = (c ⟨n, hnlessnsucc⟩) := by
      simp[c]
    have c_orthog: OrthogPred β c := by


      have ind_neq_n (ind: Fin (n+1)) (h: ind ≠ ⟨n,hnlessnsucc⟩): ↑ind ≠ n := by
        show ↑ind ≠ (↑(⟨ n,hnlessnsucc⟩: Fin (n+1)): ℕ)
        have: ↑(⟨ n,hnlessnsucc⟩: Fin (n+1)) = n := rfl
        intro h'
        exact h (Fin.ext_iff.mpr h')

      have ind_lt_n (ind: Fin (n+1)) (h: ind ≠ ⟨n,hnlessnsucc⟩): ↑ind < n := by
        suffices ↑ind ≤ n ∧ ↑ind ≠ n from ?_
        . have ⟨h₀, h₁⟩ := this
          exact Nat.lt_of_le_of_ne h₀ h₁
        constructor
        . exact Nat.le_of_lt_succ ind.is_lt
        . exact ind_neq_n ind h


      have hc_eq_c'_on_ind_neq_n (ind: Fin (n+1)) (h: ind ≠ ⟨n,hnlessnsucc⟩): c ind = c'.toFun ⟨↑ind,ind_lt_n ind h⟩ := by
        have hj_neq_n: ↑ind ≠ n := by exact Nat.ne_of_lt (ind_lt_n ind h)
        simp only [c]
        rw[dif_pos ]
        exact hj_neq_n

      have h_one_is_n (i j: Fin (n+1)) (hjn: i ≠ j): (i=⟨n,hnlessnsucc⟩) → β (c i) (c j) = 0 := by
        intro h'
        rw[h', hs, <- hc_last]

        let j': ℕ := ↑j
        have hj': j'<(n+1) := j.is_lt
        let i': ℕ := ↑i
        have hi': i'<(n+1) := i.is_lt
        have hi'n_eq: i'=n := by exact Fin.mk.inj_iff.mp h'

        have hi'n_neq: i'≠ j' := Fin.val_ne_iff.mpr hjn

        have hj_neq_n: j ≠ ⟨n,hnlessnsucc⟩ := by
          rw[<- h']
          symm
          exact Fin.val_ne_iff.mp hi'n_neq

        have j_ineq: j'<n := ind_lt_n j hj_neq_n

        rw[hc_eq_c'_on_ind_neq_n]
        apply c_orthog_rest_last
        exact hj_neq_n

      have h_none_is_n (i j: Fin (n+1)) (h: i ≠ j): (i≠ ⟨n,hnlessnsucc⟩) → (j ≠ ⟨n,hnlessnsucc⟩) → β (c i) (c j) = 0 := by
        intro h₁ h₂
        let j': ℕ := ↑j
        have hj': j'<(n+1) := j.is_lt
        let i': ℕ := ↑i
        have hi': i'<(n+1) := i.is_lt

        have hi'n_neq: i'≠ j' := by
          intro h''
          have: i=j := by
            suffices ⟨i', hi'⟩ =(⟨j', hj'⟩ : Fin (n+1)) from ?_
            . tauto
            rw[Fin.mk.inj_iff]
            exact h''
          apply h this

        have hi'_neq_n : i' ≠ n := ind_neq_n i h₁
        have hj'_neq_n : j' ≠ n := ind_neq_n j h₂

        have hi'_lt_n: i'<n := ind_lt_n i h₁
        have hj'_lt_n: j'<n := ind_lt_n j h₂

        let i_new: Fin n := ⟨i', hi'_lt_n⟩
        let j_new: Fin n := ⟨j', hj'_lt_n⟩
        rw[hc_eq_c'_on_ind_neq_n,hc_eq_c'_on_ind_neq_n]
        apply c'.orthog
        intro hcontr
        rw[Fin.mk.inj_iff] at hcontr
        . exact hi'n_neq hcontr
        . exact h₁
        . exact h₂

      intro i j h
      let h1:= (i ≠ ⟨n,hnlessnsucc⟩ ) ∧ (j ≠ ⟨n,hnlessnsucc⟩)
      let h2:= (i = ⟨n,hnlessnsucc⟩ )
      let h3:= (j = ⟨n,hnlessnsucc⟩)
      have: h1 ∨ h2 ∨ h3 := by
        rcases Classical.em (i=⟨ n,hnlessnsucc⟩) with h₁ | h₁
        . right; left; exact h₁
        . rcases Classical.em (j=⟨ n,hnlessnsucc⟩) with h₃ | h₄
          . right; right; exact h₃
          . left; exact ⟨ h₁, h₄⟩

      rcases this with h1' | (h2' | h3')
      . apply h_none_is_n i j h h1'.left h1'.right
      . apply h_one_is_n i j h h2'
      . rw[hs (c i) (c j)]
        apply h_one_is_n j i h.symm h3'

    /-
    TODO: The only thing left to do is prove c_last ≠ 0. This will require showing that
      span is preserved by orthog_by_gs (so add more to OrthogNonZero)

    Once proof completed refactor to avoid using a class, and just have a definition of
      c: Fin n → V given b: Fin n → V
    then create a theorem that proves c is linearly independent and orthogonal if b is linearly independent.
    -/
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
