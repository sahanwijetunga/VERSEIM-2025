
import Mathlib.Tactic
#check [1,2,3]



#check ([]: List ℕ)

namespace Hidden
inductive List (α: Type) where
  | nil: List α
  | cons : α → List α → List α

end Hidden

example: [1,2] = List.cons 1 (List.cons 2 []) := rfl

def reverse {α: Type}: List α → List α
  | [] => []
  | List.cons a xs => reverse xs ++ [a]

