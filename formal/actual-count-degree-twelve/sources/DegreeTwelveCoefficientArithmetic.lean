import DegreeTwelveRabinCriterion
import Mathlib.Tactic.Ring

/-! Executable coefficient-list arithmetic with proved polynomial semantics.
Concrete certificates can be reduced by the kernel without expanding one
large symbolic product through the ring tactic. -/
namespace StackSorting.DegreeTwelve.Coefficients
open Polynomial
abbrev F := ZMod 17
instance : Fact (Nat.Prime 17) := ⟨by decide⟩

def add : List F → List F → List F
  | [], b => b
  | a, [] => a
  | a :: as, b :: bs => (a+b) :: add as bs

def neg : List F → List F := List.map (fun a => -a)

def scale (a : F) : List F → List F
  | [] => []
  | b :: bs => (a*b) :: scale a bs

def mul : List F → List F → List F
  | [], _ => []
  | a :: as, b => add (scale a b) (0 :: mul as b)

def pad (n : Nat) (a : List F) : List F := a ++ List.replicate (n-a.length) 0

def frobenius : List F → List F
  | [] => []
  | a :: as => add [a] (List.replicate 17 0 ++ frobenius as)

noncomputable def eval : List F → F[X]
  | [] => 0
  | a :: as => C a + X * eval as

theorem eval_add (a b : List F) : eval (add a b) = eval a + eval b := by
  induction a generalizing b with
  | nil => simp [add, eval]
  | cons a as ih =>
    cases b with
    | nil => simp [add, eval]
    | cons b bs => simp only [add, eval, ih, C_add]; ring

theorem eval_neg (a : List F) : eval (neg a) = -eval a := by
  induction a with
  | nil => simp [neg, eval]
  | cons a as ih => simp only [neg, List.map_cons, eval, C_neg] at *; rw [ih]; ring

theorem eval_scale (a : F) (b : List F) : eval (scale a b) = C a * eval b := by
  induction b with
  | nil => simp [scale, eval]
  | cons b bs ih => simp only [scale, eval, ih, C_mul]; ring

theorem eval_mul (a b : List F) : eval (mul a b) = eval a * eval b := by
  induction a with
  | nil => simp [mul, eval]
  | cons a as ih => simp only [mul, eval_add, eval_scale, eval, C_0, zero_add, ih]; ring

theorem eval_append (a b : List F) :
    eval (a ++ b) = eval a + X^a.length * eval b := by
  induction a with
  | nil => simp [eval]
  | cons a as ih =>
    simp only [List.cons_append, eval, ih, List.length_cons, pow_succ]
    ring

theorem eval_zeroes (n : Nat) : eval (List.replicate n (0 : F)) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, eval, ih]

theorem eval_pad (n : Nat) (a : List F) : eval (pad n a) = eval a := by
  simp [pad, eval_append, eval_zeroes]

theorem eval_frobenius (a : List F) : eval (frobenius a) = (eval a)^17 := by
  induction a with
  | nil => simp [frobenius, eval]
  | cons a as ih =>
    have ha : a^17 = a := by simp
    simp only [frobenius, eval_add, eval_append, eval_zeroes, List.length_replicate,
      eval, mul_zero, add_zero, zero_add, ih, add_pow_char, mul_pow]
    rw [← C_pow, ha]

theorem equality_of_padded_equality {n : Nat} {a b : List F}
    (h : pad n a = pad n b) : eval a = eval b := by
  have he := congrArg eval h
  simpa only [eval_pad] using he

#print axioms eval_add
#print axioms eval_neg
#print axioms eval_mul
#print axioms eval_frobenius
#print axioms equality_of_padded_equality
end StackSorting.DegreeTwelve.Coefficients
