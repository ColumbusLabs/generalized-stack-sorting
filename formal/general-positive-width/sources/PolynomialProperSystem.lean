import ProperSeriesRecursion

/-!
Finite polynomial expressions evaluated as formal coefficient sequences.
The Cauchy product is defined by its finite coefficient sum. This does not
assert identification with Mathlib's `PowerSeries` type.
-/
namespace StackSorting.ProperSeries

universe u v

/-- A finite ordered sum of the first n entries. -/
def sumTerms {A : Type u} [Zero A] [Add A] (f : Nat → A) : Nat → A
  | 0 => 0
  | n + 1 => sumTerms f n + f n

theorem sumTerms_congr {A : Type u} [Zero A] [Add A]
    {f g : Nat → A} (n : Nat) (h : ∀ k, k < n → f k = g k) :
    sumTerms f n = sumTerms g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumTerms]
    rw [ih (fun k hk => h k (by omega)), h n (by omega)]

/-- The coefficient of degree n in the ordinary Cauchy product. -/
def cauchy {A : Type u} [Zero A] [Add A] [Mul A]
    (a b : Series A) (n : Nat) : A :=
  sumTerms (fun k => a k * b (n - k)) (n + 1)

/-- Multiplication by the formal variable x. -/
def shift {A : Type u} [Zero A] (a : Series A) : Series A
  | 0 => 0
  | n + 1 => a n

/-- Finite arithmetic syntax with scalar coefficients, x and unknowns.
Powers and finite sums are represented by repeated multiplication/addition. -/
inductive PolyExpr (I : Type v) (A : Type u) where
  | scalar (c : A)
  | x
  | unknown (i : I)
  | add (a b : PolyExpr I A)
  | mul (a b : PolyExpr I A)
  | neg (a : PolyExpr I A)

/-- Literal coefficient semantics for a finite polynomial expression. -/
def PolyExpr.eval {I : Type v} {A : Type u}
    [Zero A] [One A] [Add A] [Mul A] [Neg A]
    (e : PolyExpr I A) (a : Family I A) : Series A :=
  match e with
  | .scalar c => fun n => if n = 0 then c else 0
  | .x => fun n => if n = 1 then 1 else 0
  | .unknown i => a i
  | .add e f => fun n => e.eval a n + f.eval a n
  | .mul e f => cauchy (e.eval a) (f.eval a)
  | .neg e => fun n => -(e.eval a n)

/-- Coefficients below n of an arithmetic expression depend only on the
unknown coefficients below n. The multiplication case uses exactly k+(d-k)=d. -/
theorem PolyExpr.eval_causal {I : Type v} {A : Type u}
    [Zero A] [One A] [Add A] [Mul A] [Neg A]
    (e : PolyExpr I A) {n : Nat} {a b : Family I A}
    (h : AgreeBelow n a b) :
    ∀ k, k < n → e.eval a k = e.eval b k := by
  induction e with
  | scalar c => intro k hk; rfl
  | x => intro k hk; rfl
  | unknown i => exact h i
  | add e f ihe ihf =>
    intro k hk
    change e.eval a k + f.eval a k = e.eval b k + f.eval b k
    rw [ihe k hk, ihf k hk]
  | mul e f ihe ihf =>
    intro d hd
    apply sumTerms_congr
    intro k hk
    have hk' : k < n := by omega
    have hd' : d - k < n := by omega
    rw [ihe k hk', ihf (d - k) hd']
  | neg e ihe =>
    intro k hk
    exact congrArg Neg.neg (ihe k hk)

/-- The operator whose fixed-point equation is y = x R(x,y). -/
def properStep {I : Type v} {A : Type u}
    [Zero A] [One A] [Add A] [Mul A] [Neg A]
    (R : I → PolyExpr I A) (a : Family I A) : Family I A :=
  fun i => shift ((R i).eval a)

theorem properStep_contracting {I : Type v} {A : Type u}
    [Zero A] [One A] [Add A] [Mul A] [Neg A]
    (R : I → PolyExpr I A) : Contracting (properStep R) := by
  intro n a b h i k hk
  cases k with
  | zero => rfl
  | succ k => exact (R i).eval_causal h k (by omega)

/-- Explicit coefficient recursion for the unique solution. -/
def properSolution {I : Type v} {A : Type u}
    [Zero A] [One A] [Add A] [Mul A] [Neg A]
    (R : I → PolyExpr I A) : Family I A :=
  solution (properStep R) (fun _ _ => 0)

theorem properSolution_equation {I : Type v} {A : Type u}
    [Zero A] [One A] [Add A] [Mul A] [Neg A]
    (R : I → PolyExpr I A) (i : I) :
    properSolution R i = shift ((R i).eval (properSolution R)) := by
  exact congrFun (solution_fixed (properStep_contracting R) (fun _ _ => 0)).symm i

/-- Every finite polynomial right-hand side defines one and only one vector
of formal coefficient sequences solving y = x R(x,y). -/
theorem proper_exists_unique {I : Type v} {A : Type u}
    [Zero A] [One A] [Add A] [Mul A] [Neg A]
    (R : I → PolyExpr I A) :
    ∃ a : Family I A,
      (∀ i, a i = shift ((R i).eval a)) ∧
      ∀ b, (∀ i, b i = shift ((R i).eval b)) → b = a := by
  refine ⟨properSolution R, properSolution_equation R, ?_⟩
  intro b hb
  apply fixed_unique (properStep_contracting R)
  · funext i
    exact (hb i).symm
  · exact solution_fixed (properStep_contracting R) (fun _ _ => 0)

/-- All constant coefficients are forced to zero. -/
theorem properSolution_zero {I : Type v} {A : Type u}
    [Zero A] [One A] [Add A] [Mul A] [Neg A]
    (R : I → PolyExpr I A) (i : I) : properSolution R i 0 = 0 := by
  exact congrFun (properSolution_equation R i) 0

/-- The (n+1)-st coefficient is obtained by evaluating R at degree n. -/
theorem properSolution_succ {I : Type v} {A : Type u}
    [Zero A] [One A] [Add A] [Mul A] [Neg A]
    (R : I → PolyExpr I A) (i : I) (n : Nat) :
    properSolution R i (n + 1) = (R i).eval (properSolution R) n := by
  exact congrFun (properSolution_equation R i) (n + 1)

/-- The first n coefficients are already exact after n finite iterations. -/
theorem properSolution_finite_prefix {I : Type v} {A : Type u}
    [Zero A] [One A] [Add A] [Mul A] [Neg A]
    (R : I → PolyExpr I A) (n : Nat) :
    AgreeBelow n (properSolution R) (iterate (properStep R) (fun _ _ => 0) n) :=
  solution_agree_iterate (properStep_contracting R) (fun _ _ => 0) n

#print axioms PolyExpr.eval_causal
#print axioms properStep_contracting
#print axioms proper_exists_unique
#print axioms properSolution_finite_prefix

end StackSorting.ProperSeries
