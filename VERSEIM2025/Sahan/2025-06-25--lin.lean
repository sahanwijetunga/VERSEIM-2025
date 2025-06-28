import Mathlib.Tactic

import Mathlib.Data.FinEnum

#check Finsupp.single

-- noncomputable
-- def f : Fin 3 → ℚ := ↑(Finsupp.single 0 1)

@[simp]
def f : Fin 3 → ℕ
  | 0 => 1
  | 1 => 0
  | 2 => 0

example : Pi.single (0:Fin 3) 1 = ↑(Finsupp.single (0:Fin 3) 1) := by
  ext i
  match i with
   | 0 => simp
   | 1 => simp
   | 2 => simp


-- example : f = Pi.single (0:Fin 3) 1 := by
--   ext
--   simp

example : f (1:Fin 3) = 0 := by rfl


example : f = ![(1:ℕ),0,0] := by
  decide




#check ![(1:ℕ),0,0]

example : ¬ (![(1:ℕ),0,0] = ![0,1,0]) := by
  intro a
  have x : 1 = 0 :=
    congrFun a 0
  exact one_ne_zero x

example : ¬ (![(1:ℕ),0,0] = ![0,1,0]) := by
  intro a
  exact one_ne_zero (congrFun a 0)


theorem fun_ne {X Y : Type} {f g : X → Y} {a : X} (hne : f a ≠ g a) : f ≠ g := by
  intro heq

  exact hne (congrFun heq a)

example : ![(1:ℕ),0,0,0] ≠ ![0,(1:ℕ),0,0] := by
  let f : Fin 4 → ℕ := ![(1:ℕ),0,0,0]
  let g : Fin 4 → ℕ := ![0,(1:ℕ),0,0]
  have h : f 0 ≠ g 0 := by
    unfold f
    unfold g
    simp
  exact fun_ne h



example : ![(1:ℕ),0,0,0] = ![(1:ℕ),0,0,0] := by
  rfl

example : ![(1:ℕ),0,0,0] ≠ ![0,(1:ℕ),0,0] := by
  have h : ![(1:ℕ),0,0,0] 0 ≠ ![0,(1:ℕ),0,0] 0 := by
    simp
  exact fun_ne h

example : [(1:ℕ),0,0,0] ≠ [0,1,0,0] := by trivial

#eval ![(1:ℕ),0,0,0] == ![0,1,0,0]

-- #eval ![(1:k),0,0,0] == ![0,1,0,0]

example : ![(1:ℕ),0,0,0] ≠ ![0,1,0,0] := by
  exact not_eq_of_beq_eq_false rfl

example (n:ℕ) : DecidableEq (Fin n → ℕ) := inferInstance


-- def ff:  :=
--   if h:![(1:ℕ),0,0,0] ≠ ![0,(1:ℕ),0,0] then "ne" else "eq"

-- #eval ff


variable (s:Finset (Fin 3))

-- #eval (Finset.univ:Finset (Fin 3)).toList


#check FinEnum

example : List (Fin 5) := FinEnum.toList (Fin 5)

#eval FinEnum.toList (Fin 15)

example : Pi.single (0:Fin 3) 1 = ↑(Finsupp.single (0:Fin 3) 1) := by
  ext i
  have ls := FinEnum.toList (Fin 3)
  match i with
   | 0 => simp
   | 1 => simp
   | 2 => simp


#check List.recOn



example (α:Type) (f g :Fin 5 → α) (h:(i:Fin 5) → f i = g i) : f = g := by
  ext i
  exact h i

example (α:Type) (f g :Fin 5 → α) (j:Fin 5) (h: f j ≠ g j) : f ≠ g := by
  intro k
  rw [k] at h
  exact h rfl

-- example : ![1,0,0] ≠ ![0,1,0] := by
--   intro k
--   sorry


example : List ( (Fin 5) × ℕ ) := List.map (fun (i:Fin 5) => (i,i.toNat.succ)) (FinEnum.toList (Fin 5))

#eval List.map (fun (i:Fin 5) => (i,i.toNat.succ)) (FinEnum.toList (Fin 5))

#check funext
