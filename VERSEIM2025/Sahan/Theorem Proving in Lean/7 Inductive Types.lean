import Mathlib.Tactic

namespace Hidden1

-- def add (m n : Nat) : Nat :=
--   match n with
--   | Nat.zero   => m
--   | Nat.succ n => Nat.succ (add m n)

-- instance : Add Nat where
--   add := add

def mul (m n : Nat) : Nat :=
  match n with
  | Nat.zero => Nat.zero
  | Nat.succ n => mul m n + m

instance : Mul Nat where
  mul := mul

@[simp]
theorem mul_succ (m n : Nat) : m * (n+1)=m*n+m := rfl


@[simp]
theorem mul_zero (n : Nat) : n*0 = 0 := rfl

@[simp]
theorem zero_mul (n: Nat) : 0*n=0 := by
  induction n
  case zero => rfl
  case succ n h =>
    simp_all

@[simp]
theorem mul_one (m : Nat) : m * 1= m := by
  simp_all

@[simp]
theorem one_mul (n: Nat) : 1*n= n := by
  induction n
  case zero => rfl
  case succ n h => simp_all


@[simp]
theorem succ_mul (m n : Nat) : (m+1)*n = m*n+n := by
  induction n
  case zero => simp_all
  case succ n h =>
    calc
      (m + 1) * (n + 1) = (m+1)*n+(m+1) := by simp
      _ = (m*n+n)+(m+1) := by simpa
      _ = m*(n+1)+n+1 := by
        rw[mul_succ]
        abel

theorem mul_add (a b c : Nat) : a*(b+c)=a*b+a*c := by
  induction c
  case zero => simp
  case succ c h =>
    show a*(b+c)+a = a*b+(a*c+a)
    rw[h]
    abel

theorem mul_comm (m n : Nat) : n*m=m*n := by
  induction n
  case zero => simp_all
  case succ n h =>
    simp_all

def pred (n : Nat) : Nat :=
  match n with
  | Nat.zero => 0
  | Nat.succ n => n

@[simp]
theorem pred_succ (n: Nat): pred (n+1) = n := by
  induction n
  repeat rfl

@[simp]

theorem succ_pred (n: Nat) (h: n ≠ 0): (pred n)+1=n := by
  cases n
  . contradiction
  . rfl

def sub (m n : Nat): Nat :=
  match n with
  | Nat.zero => m
  | Nat.succ n => sub (pred m) n

instance: Sub Nat where
  sub := sub

@[simp]
theorem pred_eq_sub_1 (n: Nat): n-1 = pred n := rfl

@[simp]
theorem sub_succ (m n : Nat) : m-(n+1) = (m-1)- n := rfl

@[simp]
theorem sub_self (n : Nat): n-n=0 := by
  induction n
  case zero => rfl
  case succ n h =>
    abel_nf
    show n-n=0
    exact h

@[simp]
theorem add_sub (m n : Nat): (m+n)-n = m := by
  induction n
  case zero => rfl
  case succ n h =>
    rw[sub_succ]
    show pred ((m+n)+1)-n=m
    rw[pred_succ]
    exact h

end Hidden1

namespace Hidden2

@[simp]
def length {α} (l: List α): Nat :=
  match l with
  | List.nil => 0
  | List.cons _ as => length as+1

@[simp]
theorem length_add (xs ys : List α) : length (xs++ys)=length xs + length ys := by
  induction xs
  case nil =>
    show length (ys) = 0+length ys
    simp
  case cons a as h =>
    dsimp
    rw[h]
    abel

@[simp]
def reverse {α} (l: List α): List α :=
  match l with
  | List.nil => []
  | List.cons a as => reverse as++[a]

theorem length_reverse (xs: List α): length (reverse xs) = length xs := by
  induction xs
  case nil => rfl
  case cons x xs h =>
    show length (reverse xs++[x]) = length ([x]++xs)
    simpa

@[simp]
theorem reverse_add (xs ys: List α): reverse (xs++ys) = reverse ys++reverse xs := by
  induction xs
  case nil => simp
  case cons x xs h =>
    simp_all

theorem reverse_reverse (xs: List α): reverse (reverse xs) = xs := by
  induction xs
  case nil => rfl
  case cons x xs h =>
    simp_all

end Hidden2


namespace Hidden3

inductive Term where
  | const (n: Nat): Term
  | var (n: Nat): Term
  | plus (s t: Term): Term
  | times (s t: Term): Term

def eval_term (f: Nat -> Nat) (t: Term) : Nat :=
  match t with
  | Term.const n => n
  | Term.var n => f n
  | Term.plus s t => eval_term f s + eval_term f t
  | Term.times s t => eval_term f s * eval_term f t

open Term
#eval eval_term (fun x => x^2+1) (plus (const 5) (var 3))

end Hidden3

namespace Hidden4

inductive PropFormula where
  | True
  | False
  | var (n: Nat)
  | and (A B : PropFormula)
  | or (A B: PropFormula)
  | not (A: PropFormula)
  | implies (A B: PropFormula)

def eval_prop_formula (f: Nat -> Bool) (A: PropFormula): Bool :=
  match A with
  | PropFormula.True => true
  | PropFormula.False => false
  | PropFormula.var n => f n
  | PropFormula.or A B => (eval_prop_formula f A) ∨  (eval_prop_formula f B)
  | PropFormula.and A B => (eval_prop_formula f A) ∧  (eval_prop_formula f B)
  | PropFormula.implies A B => (eval_prop_formula f A) → (eval_prop_formula f B)
  | PropFormula.not A => ¬ (eval_prop_formula f A)

def complexity (A: PropFormula): Nat :=
  match A with
  | PropFormula.True => 1
  | PropFormula.False => 1
  | PropFormula.var _ => 2
  | PropFormula.and A B => complexity A + complexity B + 1
  | PropFormula.or A B => complexity A + complexity B + 1
  | PropFormula.implies A B => complexity A + complexity B + 1
  | PropFormula.not A => complexity A + 1


def subs_formula (A B: PropFormula) (n: Nat): PropFormula :=
    match A with
  | PropFormula.True => PropFormula.True
  | PropFormula.False => PropFormula.False
  | PropFormula.var m => if (m=n) then B else PropFormula.var m
  | PropFormula.or A C => PropFormula.or (subs_formula A B n)  (subs_formula A C n)
  | PropFormula.and A C => PropFormula.and (subs_formula A B n)  (subs_formula A C n)
  | PropFormula.implies A C => PropFormula.implies (subs_formula A B n)  (subs_formula A C n)
  | PropFormula.not A => PropFormula.not (subs_formula A B n)


#eval (eval_prop_formula (fun x => x ≥ 2) (PropFormula.False.or (PropFormula.var 2)))
#eval (complexity (PropFormula.False.or (PropFormula.var 2)))



end Hidden4
