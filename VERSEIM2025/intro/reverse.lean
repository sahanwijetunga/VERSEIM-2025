import Mathlib.Tactic

-- lists

#check [ 1,2,3]

#check ([]:List ℕ)

#check (List.cons 3 [1,2])

-- defn of list is more-or-less as follows
-- def List (α:Type) where
-- | nil : List α
-- | cons : α → List α → List α 

example : [1,2] = List.cons 1 (List.cons 2 []) := rfl

def f : ℕ → ℕ 
 | Nat.zero => 0
 | _+1 => 1

def f' :ℕ→ ℕ := fun n =>
 match n with
 | Nat.zero => 0
 | _+1 => 1

-- let's write code to reverse a list

#check List.append

#eval List.append [1,2] [3] 



def reverse {α:Type}  : List α → List α 
  | [] => [] 
  | List.cons x xs => List.append (reverse xs)  [ x ] 


def reverse' {α:Type}  : List α → List α 
  | [] => [] 
  | List.cons x xs =>  (reverse xs) ++ [ x ] 

#eval reverse [1,2,3,4,5]

#eval reverse [ "a", "b", "ccc" ]
