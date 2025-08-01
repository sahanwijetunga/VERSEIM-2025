import Mathlib.Tactic

set_option linter.unusedVariables false
inductive Vect (α : Type u) : Nat → Type u
  | nil  : Vect α 0
  | cons : α → {n : Nat} → Vect α n → Vect α (n+1)
namespace Vect
def head : {n : Nat} → Vect α (n+1) → α
  | n, cons a as => a

def tail : {n : Nat} → Vect α (n+1) → Vect α n
  | n, cons a as => as

theorem eta : ∀ {n : Nat} (v : Vect α (n+1)), cons (head v) (tail v) = v
  | n, cons a as => rfl

def map (f : α → β → γ) : {n : Nat} → Vect α n → Vect β n → Vect γ n
  | 0,   nil,       nil       => nil
  | n+1, cons a as, cons b bs => cons (f a b) (map f as bs)

def zip : {n : Nat} → Vect α n → Vect β n → Vect (α × β) n
  | 0,   nil,       nil       => nil
  | n+1, cons a as, cons b bs => cons (a, b) (zip as bs)

def zip' : {n : Nat} → Vect α n → Vect β n → Vect (α × β) n := by
  apply map
  exact fun a b => (a,b)

example (n: Nat) (as: Vect α n) (bs: Vect β n ) : zip as bs = zip' as bs := by
  sorry

end Vect
